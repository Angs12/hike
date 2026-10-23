#!/usr/bin/env python3
"""Generates the glibc signature file Hike reads (data/glibc.sexp).

Inputs, all from the machine's own C library:
  * the exported function symbols and their symbol versions, from each
    library's `.dynsym` (readelf);
  * their prototypes and `const` / `pure` / `noreturn` / variadic facts,
    from the system headers through clang's AST;
  * the facts headers do not state, from annotations.py.

A symbol with no header prototype, or one whose type Hike's System V model
cannot express, is left out: a call to it keeps the generic convention.

Usage: generate.py [--clang clang] [--out data/glibc.sexp] [LIB ...]
"""

import argparse
import glob
import json
import os
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import annotations as ann  # noqa: E402

LIBDIR = "/lib/x86_64-linux-gnu"
LIBRARIES = ["libc.so.6", "libm.so.6", "libresolv.so.2", "libanl.so.1"]
INCLUDE = "/usr/include"

# ---------------------------------------------------------------- symbols


def library_symbols(lib):
    """(symbol, version) for every defined function of a library."""
    out = subprocess.run(
        ["readelf", "--dyn-syms", "--wide", os.path.join(LIBDIR, lib)],
        capture_output=True, text=True, check=True).stdout
    found = []
    for line in out.splitlines():
        cols = line.split()
        if len(cols) < 8 or cols[3] not in ("FUNC", "IFUNC") or cols[6] == "UND":
            continue
        name = cols[7]
        if "@" not in name:
            continue
        symbol, _, version = name.partition("@")
        found.append((symbol, version.lstrip("@")))
    return found


# ------------------------------------------------------------------ types

QUALIFIERS = re.compile(
    r"\b(const|volatile|restrict|__restrict|__restrict__|_Nonnull|_Nullable"
    r"|_Atomic|register)\b")

BASE = {
    "char": "Char", "signed char": "Char", "unsigned char": "Char",
    "short": "Short", "short int": "Short", "signed short": "Short",
    "unsigned short": "Short", "unsigned short int": "Short",
    "int": "Int", "signed": "Int", "signed int": "Int", "unsigned": "Int",
    "unsigned int": "Int",
    "long": "Long", "long int": "Long", "signed long": "Long",
    "unsigned long": "Long", "unsigned long int": "Long",
    "long long": "Long_long", "long long int": "Long_long",
    "unsigned long long": "Long_long", "unsigned long long int": "Long_long",
    "_Bool": "Bool",
    "float": "Float", "double": "Double", "long double": "Long_double",
    "__int128": "Int128", "unsigned __int128": "Int128",
    "_Float128": "Float128", "__float128": "Float128",
    "_Float16": "Float16", "_Float32": "Float", "_Float64": "Double",
    "_Float32x": "Double", "_Float64x": "Long_double",
}

COMPLEX = {
    "_Complex float": "Float", "_Complex double": "Double",
    "_Complex long double": "Long_double", "_Complex _Float16": "Float16",
    "_Complex _Float32": "Float", "_Complex _Float64": "Double",
}


def clean(text):
    text = re.sub(r"__attribute__\(\(.*?\)\)", "", text)
    text = QUALIFIERS.sub("", text)
    text = re.sub(r"\b(struct|union|enum)\s+", lambda m: m.group(1) + " ", text)
    return re.sub(r"\s+", " ", text).strip()


class Types:
    def __init__(self):
        self.typedefs = {}

    def add_typedef(self, name, qual):
        self.typedefs.setdefault(name, qual)

    def ctype(self, text, depth=0):
        """The Hike_sysv type of a C type string, or None when unsupported."""
        if depth > 12:
            return None
        text = clean(text)
        if not text:
            return None
        if "*" in text or "(" in text or "[" in text:
            return "Pointer"
        if text in BASE:
            return BASE[text]
        if text in COMPLEX:
            return "(Complex %s)" % COMPLEX[text]
        if text.startswith("enum "):
            return "Int"
        if text in ann.AGGREGATES:
            return ann.AGGREGATES[text]
        if text in self.typedefs:
            return self.ctype(self.typedefs[text], depth + 1)
        return None


def split_function_type(qual):
    """(return text, [parameter texts], variadic, noreturn) of a function
    type string such as 'int (const char *, ...) __attribute__((noreturn))'."""
    noreturn = "noreturn" in qual
    qual = re.sub(r"\s*__attribute__\(\(.*?\)\)\s*$", "", qual).strip()
    if not qual.endswith(")"):
        return None
    depth = 0
    for i in range(len(qual) - 1, -1, -1):
        c = qual[i]
        if c == ")":
            depth += 1
        elif c == "(":
            depth -= 1
            if depth == 0:
                ret = qual[:i].strip()
                body = qual[i + 1:-1]
                break
    else:
        return None
    if ret.endswith("(*") or ret.endswith("*(") or "(" in ret:
        return None  # a function returning a function pointer
    params, level, current = [], 0, ""
    for c in body:
        if c == "," and level == 0:
            params.append(current.strip())
            current = ""
            continue
        level += (c in "([") - (c in ")]")
        current += c
    if current.strip():
        params.append(current.strip())
    variadic = bool(params) and params[-1] == "..."
    if variadic:
        params = params[:-1]
    if params == ["void"]:
        params = []
    return ret, params, variadic, noreturn


# ----------------------------------------------------------------- headers


def headers():
    names = sorted(glob.glob(INCLUDE + "/*.h"))
    for sub in ("sys", "arpa", "net", "netinet", "netinet6", "linux",
                "scsi", "rpc", "rpcsvc", "sys"):
        names += sorted(glob.glob("%s/%s/*.h" % (INCLUDE, sub)))
    names += sorted(glob.glob(INCLUDE + "/x86_64-linux-gnu/sys/*.h"))
    return names


def collect(clang, wanted, types):
    """name -> function node, from every header's AST."""
    functions = {}
    for header in headers():
        rel = os.path.relpath(header, INCLUDE)
        with tempfile.NamedTemporaryFile("w", suffix=".c", delete=False) as f:
            f.write("#define _GNU_SOURCE 1\n#include <%s>\n" % rel)
            source = f.name
        try:
            run = subprocess.run(
                [clang, "-fsyntax-only", "-O2", "-D_FORTIFY_SOURCE=2",
                 "-Xclang", "-ast-dump=json", source],
                capture_output=True, text=True)
        finally:
            os.unlink(source)
        if not run.stdout.strip():
            continue
        try:
            tree = json.loads(run.stdout)
        except json.JSONDecodeError:
            continue
        for node in tree.get("inner", []):
            kind = node.get("kind")
            if kind == "TypedefDecl":
                types.add_typedef(node["name"], node["type"]["qualType"])
            elif (kind == "FunctionDecl" and node.get("name") in wanted
                  and not node.get("isImplicit")):
                functions.setdefault(node["name"], node)
    return functions


# ------------------------------------------------------------------ entries


def pointee_const(text):
    """Whether the object a pointer type points to is const."""
    text = re.sub(r"\b(restrict|__restrict|volatile|_Nonnull)\b", "", text)
    if "(" in text:
        return False
    star = text.rfind("*")
    return star > 0 and re.search(r"\bconst\b", text[:star]) is not None


def entry(lib, version, name, node, types):
    shape = split_function_type(node["type"]["qualType"])
    if shape is None:
        return None
    ret_text, param_texts, variadic, noreturn = shape
    ret = None
    if ret_text != "void":
        ret = types.ctype(ret_text)
        if ret is None:
            return None
    params = []
    declared = [n for n in node.get("inner", []) if n.get("kind") == "ParmVarDecl"]
    if len(declared) != len(param_texts):
        return None
    for text, decl in zip(param_texts, declared):
        qual = decl["type"].get("desugaredQualType") or decl["type"]["qualType"]
        original = decl["type"]["qualType"]
        ty = types.ctype(original) or types.ctype(qual)
        if ty is None:
            return None
        fields = ["(ty %s)" % ty]
        if ty == "Pointer":
            if pointee_const(qual) or pointee_const(original):
                fields.append("(access Read_only)")
            if name in ann.NONCAPTURING:
                fields.append("(captured false)")
        params.append("(" + " ".join(fields) + ")")
    attrs = {a["kind"] for a in node.get("inner", []) if "kind" in a}
    parts = ["(library %s)" % lib, "(version %s)" % version,
             "(symbol %s)" % name]
    if ret is not None:
        parts.append("(return %s)" % ret)
    parts.append("(params (%s))" % " ".join(params))
    returned = ann.RETURNED.get(name)
    if returned is not None and returned < len(params):
        parts.append("(returned %d)" % returned)
    if variadic:
        parts.append("(variadic true)")
    if noreturn or name in ann.NORETURN:
        parts.append("(noreturn true)")
    if name in ann.ARGMEM:
        read_only = params and all("Read_only" in p for p in params
                                   if "Pointer" in p)
        parts.append("(memory (Argmem %s))" %
                     ("Read_only" if read_only else "May_write"))
    elif "ConstAttr" in attrs:
        parts.append("(memory None_)")
    elif "PureAttr" in attrs:
        parts.append("(memory Reads_any)")
    return "(" + " ".join(parts) + ")"


def old_libraries(symbol):
    return [lib for lib, prefixes in ann.MOVED
            if any(symbol.startswith(p) for p in prefixes)]


def main():
    arg = argparse.ArgumentParser()
    arg.add_argument("--clang", default="clang-21")
    arg.add_argument("--out", default="data/glibc.sexp")
    arg.add_argument("libs", nargs="*", default=LIBRARIES)
    args = arg.parse_args()

    symbols = {}
    for lib in args.libs:
        for symbol, version in library_symbols(lib):
            symbols.setdefault(lib, []).append((symbol, version))
    wanted = {s for pairs in symbols.values() for s, _ in pairs}

    types = Types()
    functions = collect(args.clang, wanted, types)

    def declaration(symbol):
        node = functions.get(symbol)
        if node is None:
            for prefix in ("__isoc23_", "__isoc99_"):
                if symbol.startswith(prefix):
                    node = functions.get(symbol[len(prefix):])
        if node is None and symbol in ann.EXTRA:
            shape = split_function_type(ann.EXTRA[symbol])
            node = {"type": {"qualType": ann.EXTRA[symbol]},
                    "inner": [{"kind": "ParmVarDecl",
                               "type": {"qualType": p}} for p in shape[1]]}
        return node

    lines, missing = [], 0
    for lib in args.libs:
        for symbol, version in sorted(set(symbols.get(lib, []))):
            node = declaration(symbol)
            text = entry(lib, version, symbol, node, types) if node else None
            if text is None:
                missing += 1
                continue
            lines.append(text)
            if lib == "libc.so.6":
                for old in old_libraries(symbol):
                    lines.append(text.replace("(library %s)" % lib,
                                              "(library %s)" % old, 1))
    with open(args.out, "w") as f:
        f.write(";; Generated by tools/libc_signatures/generate.py from the\n"
                ";; system headers and the C library's symbol versions.\n"
                ";; Every compat version of a symbol is assumed to share the\n"
                ";; prototype of its default version.\n")
        f.write("\n".join(lines) + "\n")
    print("%d entries, %d symbols without a usable prototype" %
          (len(lines), missing), file=sys.stderr)


if __name__ == "__main__":
    main()

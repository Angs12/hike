#!/usr/bin/env python3
"""Compiler oracle for the System V classifier (Hike_sysv).

Generates random C function signatures (scalars, complex numbers, structs,
unions and arrays, some packed), asks clang for their LLVM lowering -- clang
applies the psABI to produce it -- and compares clang's register classes
with what Hike_sysv places.  Register exhaustion, memory arguments, hidden
return pointers and x87 values all show in the lowering.

  sysv_oracle.py [--cases N] [--seed S] [--clang clang-21] [--classify EXE]

clang is not a perfect oracle: for an aggregate over two eightbytes it
checks only the first two eightbytes against the "SSE then SSEUP" rule
(psABI 3.2.3, post-merger rule c), where gcc and the document check them
all.  When clang and Hike disagree about such an aggregate, gcc breaks the
tie: the case counts as a clang divergence only if gcc agrees with Hike.

Exit status 1 if any case disagrees for another reason.
"""

import argparse
import os
import random
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))

# name -> (C spelling, size, alignment)
SCALARS = {
    "Bool": ("_Bool", 1, 1), "Char": ("char", 1, 1), "Short": ("short", 2, 2),
    "Int": ("int", 4, 4), "Long": ("long", 8, 8),
    "Long_long": ("long long", 8, 8), "Pointer": ("void *", 8, 8),
    "Float": ("float", 4, 4), "Double": ("double", 8, 8),
    "Long_double": ("long double", 16, 16), "Int128": ("__int128", 16, 16),
    "Float16": ("_Float16", 2, 2), "Float128": ("__float128", 16, 16),
    "M64": ("V8f", 8, 8), "M128": ("V16f", 16, 16),
    "M256": ("V32f", 32, 32), "M512": ("V64f", 64, 64),
}

PRELUDE = """#include <stdint.h>
typedef float V8f __attribute__((vector_size(8)));
typedef float V16f __attribute__((vector_size(16)));
typedef float V32f __attribute__((vector_size(32)));
typedef float V64f __attribute__((vector_size(64)));"""
COMPLEX = {"Float": ("_Complex float", 8, 4), "Double": ("_Complex double", 16, 8),
           "Long_double": ("_Complex long double", 32, 16)}
SCALAR_WEIGHTS = {"Bool": 1, "Char": 3, "Short": 3, "Int": 8, "Long": 8,
                  "Long_long": 2, "Pointer": 6, "Float": 5, "Double": 6,
                  "Long_double": 1, "Int128": 1, "Float16": 1, "Float128": 1,
                  "M64": 1, "M128": 2, "M256": 1, "M512": 1}


class Ty:
    """size/align/sexp/C-spelling of a generated type."""

    def __init__(self, kind, **kw):
        self.kind = kind
        self.__dict__.update(kw)

    def size(self):
        if self.kind == "scalar":
            return SCALARS[self.name][1]
        if self.kind == "complex":
            return COMPLEX[self.name][1]
        return self.total

    def align(self):
        if self.kind == "scalar":
            return SCALARS[self.name][2]
        if self.kind == "complex":
            return COMPLEX[self.name][2]
        return self.alignment

    def sexp(self):
        if self.kind == "scalar":
            return self.name
        if self.kind == "complex":
            return "(Complex %s)" % self.name
        fields = " ".join("((offset %d) (ty %s))" % (o, t.sexp())
                          for o, t in self.members)
        return "(Aggregate ((size %d) (align %d) (fields (%s))))" % (
            self.total, self.alignment, fields)


def round_up(n, to):
    return (n + to - 1) // to * to


def scalar(name):
    return Ty("scalar", name=name)


def make_array(elem, count):
    members = [(i * elem.size(), elem) for i in range(count)]
    return Ty("array", elem=elem, count=count, members=members,
              total=elem.size() * count, alignment=elem.align())


def make_struct(rng, members_types, union, packed, ident):
    offset, members, alignment = 0, [], 1
    total = 0
    for t in members_types:
        a = 1 if packed else t.align()
        alignment = max(alignment, a)
        if union:
            members.append((0, t))
            total = max(total, t.size())
        else:
            offset = round_up(offset, a)
            members.append((offset, t))
            offset += t.size()
            total = offset
    total = round_up(total, alignment)
    return Ty("struct", members=members, total=total, alignment=alignment,
              union=union, packed=packed, ident=ident, decl=members_types)


def random_scalar(rng):
    names, weights = zip(*SCALAR_WEIGHTS.items())
    return scalar(rng.choices(names, weights)[0])


def random_type(rng, structs, depth=0):
    roll = rng.random()
    if depth < 2 and roll < 0.30:
        count = rng.randint(1, 5)
        fields = []
        for _ in range(count):
            r = rng.random()
            if r < 0.15:
                fields.append(make_array(random_scalar(rng), rng.randint(1, 4)))
            elif r < 0.25 and depth < 1:
                fields.append(random_type(rng, structs, depth + 1))
            else:
                fields.append(random_scalar(rng))
        # A packed record holding a 16-byte-aligned member is a corner
        # where clang and gcc disagree with each other; keep it out.
        packable = all(f.align() <= 8 for f in fields)
        s = make_struct(rng, fields, union=rng.random() < 0.2,
                        packed=packable and rng.random() < 0.08,
                        ident=len(structs))
        structs.append(s)
        return s
    if roll < 0.35:
        return Ty("complex", name=rng.choice(list(COMPLEX)))
    return random_scalar(rng)


def spelling(t):
    if t.kind == "scalar":
        return SCALARS[t.name][0]
    if t.kind == "complex":
        return COMPLEX[t.name][0]
    return ("union" if t.union else "struct") + " S%d" % t.ident


def declaration(t):
    members = []
    for i, (_, m) in enumerate(zip(t.members, t.decl)):
        if m.kind == "array":
            members.append("  %s m%d[%d];" % (spelling(m.elem), i, m.count))
        else:
            members.append("  %s m%d;" % (spelling(m), i))
    attr = " __attribute__((packed))" if t.packed else ""
    return "%s S%d {\n%s\n}%s;" % ("union" if t.union else "struct", t.ident,
                                   "\n".join(members), attr)


# ------------------------------------------------------------------ clang

KNOWN_ATTRS = re.compile(
    r"\b(noundef|signext|zeroext|inreg|noalias|nocapture|nonnull|readonly|"
    r"writeonly|dso_local|internal|local_unnamed_addr|align \d+|"
    r"dereferenceable\(\d+\))\b")


def split_top(text):
    parts, depth, cur = [], 0, ""
    for c in text:
        if c == "," and depth == 0:
            parts.append(cur.strip())
            cur = ""
            continue
        depth += c in "({<[" and 1 or (c in ")}>]" and -1 or 0)
        cur += c
    if cur.strip():
        parts.append(cur.strip())
    return parts


def type_tokens(text):
    text = text.strip()
    if text == "void":
        return ""
    if text.startswith("{"):
        inner = text[1:text.rindex("}")]
        return "".join(type_tokens(p) for p in split_top(inner))
    if text.startswith("<") or text in ("float", "double", "half"):
        return "S"
    if text == "x86_fp80":
        return "X"
    if text == "fp128":
        return "S"
    if text == "i128":
        return "II"
    if re.fullmatch(r"i\d+|ptr", text):
        return "I"
    raise ValueError("unknown IR type %r" % text)


def lowered(ir):
    """function number -> (return tokens, argument tokens)."""
    result = {}
    for m in re.finditer(r"^define (.*?) @f(\d+)\((.*)\) #\d+ \{$", ir, re.M):
        head, number, params = m.group(1), int(m.group(2)), m.group(3)
        ret = KNOWN_ATTRS.sub("", head).strip()
        ret = re.sub(r"\b(dso_local|internal)\b", "", ret).strip()
        tokens, sret = "", False
        for p in split_top(params):
            if "sret(" in p:
                sret = True
                continue
            if "byval(" in p:
                tokens += "M"
                continue
            p = re.sub(r"%[\w.]+$", "", p.strip())
            tokens += type_tokens(KNOWN_ATTRS.sub("", p).strip())
        ret_tokens = "M" if sret else (type_tokens(ret) or "V")
        result[number] = (ret_tokens, tokens)
    return result


def is_aggregate_over_two(t):
    return t.kind in ("struct", "array") and t.size() > 16


def hike_memory(classify, t, is_return):
    """Whether Hike places the aggregate in memory, in isolation."""
    if is_return:
        query = "((return %s) (params ()))" % t.sexp()
    else:
        query = "((params (%s)))" % t.sexp()
    out = subprocess.run([classify], input=query, capture_output=True,
                         text=True).stdout.rstrip("\n")
    ret, _, args = out.partition(" | ")
    return ret == "M" if is_return else args == "M"


def gcc_memory(t, is_return, structs_c, tmp):
    """Whether gcc places the aggregate in memory, from its assembly."""
    name = spelling(t)
    if is_return:
        body = "%s probe(%s *p) { return *p; }" % (name, name)
    else:
        body = "char probe(%s s) { return *(char *)&s; }" % name
    source = os.path.join(tmp, "gcc_probe.c")
    with open(source, "w") as f:
        f.write("\n".join([PRELUDE] + structs_c + [body]) + "\n")
    asm = subprocess.run(["gcc", "-O2", "-mavx512f", "-w", "-S", "-o", "-",
                          source], capture_output=True, text=True).stdout
    if is_return:
        return re.search(r"movq\s+%rdi, %rax", asm) is not None
    return re.search(r"\b\d+\(%rsp\)", asm) is not None


def main():
    arg = argparse.ArgumentParser()
    arg.add_argument("--cases", type=int, default=400)
    arg.add_argument("--seed", type=int, default=1)
    arg.add_argument("--clang", default="clang-21")
    arg.add_argument("--keep", help="write the generated C source here")
    arg.add_argument("--classify", default=os.path.join(
        ROOT, "_build/default/test/probe/sysv/sysv_classify.exe"))
    args = arg.parse_args()

    rng = random.Random(args.seed)
    structs, cases = [], []
    for _ in range(args.cases):
        ret = None if rng.random() < 0.25 else random_type(rng, structs)
        params = [random_type(rng, structs) for _ in range(rng.choice(
            [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12]))]
        cases.append((ret, params))

    c = [PRELUDE]
    c += [declaration(s) for s in structs]
    for n, (ret, params) in enumerate(cases):
        decl = ", ".join("%s a%d" % (spelling(p), i) for i, p in enumerate(params))
        decl = decl or "void"
        if ret is None:
            c.append("void f%d(%s) {}" % (n, decl))
        else:
            c.append("%s f%d(%s) { %s r; return r; }" % (spelling(ret), n, decl,
                                                         spelling(ret)))
    with tempfile.TemporaryDirectory() as tmp:
        source = os.path.join(tmp, "oracle.c")
        with open(source, "w") as f:
            f.write("\n".join(c) + "\n")
        if args.keep:
            with open(args.keep, "w") as f:
                f.write("\n".join(c) + "\n")
        ir = subprocess.run(
            [args.clang, "-O0", "-S", "-emit-llvm", "-w", "-mavx512f",
             "-o", "-", source],
            capture_output=True, text=True)
    if ir.returncode != 0:
        print(ir.stderr[:2000], file=sys.stderr)
        sys.exit(2)
    expected = lowered(ir.stdout)

    # one record per case: ((return T)? (params (...)))
    query = "\n".join(
        "(%s(params (%s)))" % ("(return %s) " % r.sexp() if r else "",
                               " ".join(p.sexp() for p in ps))
        for r, ps in cases)
    got = subprocess.run([args.classify], input=query, capture_output=True,
                         text=True)
    if got.returncode != 0:
        print(got.stderr[:2000], file=sys.stderr)
        sys.exit(2)
    actual = [line.split(" | ") for line in got.stdout.splitlines()]

    bad, divergent = 0, 0
    gcc_dir = tempfile.TemporaryDirectory()

    def declarations_for(t, acc=None):
        acc = [] if acc is None else acc
        for _, m in getattr(t, "members", []):
            declarations_for(m, acc)
        if t.kind == "struct":
            acc.append(declaration(t))
        return acc

    def clang_diverges(ret, params):
        disputed = [(r, True) for r in ([ret] if ret else [])
                    if is_aggregate_over_two(r)]
        disputed += [(p, False) for p in params if is_aggregate_over_two(p)]
        if not disputed:
            return False
        for t, is_return in disputed:
            decls = declarations_for(t)
            if hike_memory(args.classify, t, is_return) != gcc_memory(
                    t, is_return, decls, gcc_dir.name):
                return False
        return True

    for n, (ret, params) in enumerate(cases):
        want = expected[n]
        have = (actual[n][0], actual[n][1] if len(actual[n]) > 1 else "")
        if want != have:
            if clang_diverges(ret, params):
                divergent += 1
                continue
            bad += 1
            if bad <= 12:
                print("MISMATCH f%d: %s (%s)" % (
                    n, spelling(ret) if ret else "void",
                    ", ".join(spelling(p) for p in params)))
                print("   clang: ret=%s args=%s" % want)
                print("   hike : ret=%s args=%s" % have)
    seen = {}

    def tally(t):
        key = t.name if t.kind in ("scalar", "complex") else t.kind
        seen[(t.kind, key)] = seen.get((t.kind, key), 0) + 1
        for _, m in getattr(t, "members", []):
            tally(m)

    for ret, params in cases:
        for t in ([ret] if ret else []) + params:
            tally(t)
    memory = sum(1 for a, _ in expected.values() if a == "M")
    stack = sum(1 for _, b in expected.values() if "M" in b)
    print("covered: " + ", ".join(
        "%s=%d" % (k[1] if k[0] != "complex" else "complex-" + k[1], v)
        for k, v in sorted(seen.items())), file=sys.stderr)
    print("cases with a hidden return pointer: %d, with a memory argument: %d"
          % (memory, stack), file=sys.stderr)
    print("%d cases, %d mismatches, %d clang divergences confirmed by gcc "
          "(seed %d)" % (len(cases), bad, divergent, args.seed))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()

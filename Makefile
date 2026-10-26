# Convenience entry points for the Dune build and the gate tier.
# Dune remains the source of truth; these targets only wrap the documented
# commands from AGENTS.md and docs/validation.md.

SHELL := /bin/bash
DUNE ?= dune
OPAM ?= opam
OPAM_BIN := $(shell $(OPAM) var bin 2>/dev/null)
OPAM_LIB := $(shell $(OPAM) var lib 2>/dev/null)

HIKE_BIN := $(OPAM_BIN)/hike
HIKE_LIB := $(OPAM_LIB)/hike
HIKE_PLUGIN := $(OPAM_LIB)/bap-common/plugins/hike

CORPUS ?= /tmp/corpus-o2
EMIT ?= /tmp/hike-emit
SEMOUT ?= /tmp/hike-sem
MATRIX ?= /tmp/hike-matrix
PERFOUT ?= /tmp/hike-performance

.PHONY: help build install uninstall reinstall clean clean-installed clean-cache \
        test unit referee corpus lift allocas semantics gates matrix fresh-lift \
        performance require-opam distclean

help:
	@echo "make build             dune build @install"
	@echo "make install           build and install the plugin and hike executable"
	@echo "make reinstall         remove the installed copy first, then install"
	@echo "make uninstall         remove files listed by the current package"
	@echo "make test              dune runtest --force"
	@echo "make corpus            build the PIE corpus in $(CORPUS)"
	@echo "make lift              lift the corpus into $(EMIT)"
	@echo "make allocas           check allocations and initializers"
	@echo "make semantics         run the LLVM O2 semantic harness"
	@echo "make matrix            run the complete robustness matrix"
	@echo "make gates             corpus + lift + allocas + semantics + unit + referee"
	@echo "make performance       measure the default performance sample"
	@echo "make fresh-lift        force a full re-lift (ignore the lift cache)"
	@echo "make clean             dune clean (removes _build and build cache)"
	@echo "make clean-installed   remove the installed hike binary, library and plugin"
	@echo "make clean-cache       remove corpus, lift, semantic, matrix and perf outputs"
	@echo "make distclean         clean + clean-installed + clean-cache"

build:
	$(DUNE) build @install
	@echo "built:       _build/default/src/drive/main.exe"
	@if [ -n "$(OPAM_BIN)" ]; then echo "installs to: $(HIKE_BIN)"; fi

require-opam:
	@test -n "$(OPAM_BIN)" -a -n "$(OPAM_LIB)" || \
		{ echo "make: no opam switch (run 'eval $$(opam env)' or set OPAM)" >&2; exit 2; }

install: build require-opam
	$(DUNE) install
	@echo "hike installed: $(HIKE_BIN)"

uninstall:
	$(DUNE) uninstall

reinstall: clean-installed
	$(DUNE) build @install
	$(DUNE) install
	@echo "hike installed: $(HIKE_BIN)"

test: unit

unit:
	$(DUNE) runtest --force

referee:
	$(DUNE) exec test/unit/test_clp_equiv.exe

corpus:
	bash test/gate/compile_corpus.sh "$(CORPUS)"

lift: install
	HIKE_EXE="$(HIKE_BIN)" \
	HIKE_CORPUS="$(CORPUS)" HIKE_EMIT="$(EMIT)" bash test/gate/gate.sh lift

fresh-lift: install
	HIKE_EXE="$(HIKE_BIN)" \
	FRESH=1 HIKE_CORPUS="$(CORPUS)" HIKE_EMIT="$(EMIT)" \
		bash test/gate/gate.sh lift

allocas: install
	HIKE_EXE="$(HIKE_BIN)" \
	HIKE_CORPUS="$(CORPUS)" HIKE_EMIT="$(EMIT)" bash test/gate/gate.sh allocas

semantics: install
	HIKE_EXE="$(HIKE_BIN)" \
	HIKE_CORPUS="$(CORPUS)" HIKE_EMIT="$(EMIT)" HIKE_SEMOUT="$(SEMOUT)" \
		bash test/gate/gate.sh semantics

gates: install corpus
	HIKE_EXE="$(HIKE_BIN)" \
	HIKE_CORPUS="$(CORPUS)" HIKE_EMIT="$(EMIT)" HIKE_SEMOUT="$(SEMOUT)" \
		bash test/gate/gate.sh all

matrix: install
	HIKE_EXE="$(HIKE_BIN)" HIKE_MATRIX="$(MATRIX)" bash test/gate/matrix.sh

performance: install
	HIKE_EXE="$(HIKE_BIN)" HIKE_PERFOUT="$(PERFOUT)" HIKE_CORPUS="$(CORPUS)" \
		bash test/gate/gate.sh performance

clean:
	$(DUNE) clean

clean-installed: require-opam
	rm -rf "$(HIKE_BIN)" "$(HIKE_LIB)" "$(HIKE_PLUGIN)"

clean-cache:
	rm -rf "$(CORPUS)" "$(EMIT)" "$(SEMOUT)" "$(MATRIX)" "$(PERFOUT)"

distclean: clean clean-installed clean-cache

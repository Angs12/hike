PROGSFOLDER=./progs/

# hike — build + install the plugin bundle.
#
# Principle #6 / provenance (2026-09-03): the build ALWAYS runs
# [bapbuild -clean] first (measured ~28s — the stale-module-cache class it
# kills is real: an identical-source rebuild once shipped 22 entry-edge
# poison phis because bapbuild reused stale .cmo files; source identity
# cannot see the artifact cache), and the install records its PROVENANCE
# next to the bundle so [scripts/battery.sh] can fail on mismatch instead
# of guessing from mtimes.
hike:
	bapbuild -clean
	bapbuild hike.plugin -pkg llvm -pkg hike.cbat_vsa
	bapbundle install hike.plugin
	@bash record_provenance.sh

clean:
	bapbuild -clean
	dune clean
	find ./progs -type f -not -name '*.c' -not -name '*.h' -delete
	rm -rf plugins

compileO0_fizzbuzz:
	gcc -O0 -o $(PROGSFOLDER)fizzbuzz_0 $(PROGSFOLDER)fizzbuzz.c
	bap --pass=hike-convlir --hike-output fizzbuzz.ll $(PROGSFOLDER)fizzbuzz_0
	clang -O3 fizzbuzz.ll -o $(PROGSFOLDER)fizzbuzz_llvmO0

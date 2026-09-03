PROGSFOLDER=./progs/

# hike — build + install the plugin; always clean first, then record
# provenance next to the bundle for battery.sh to verify.
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

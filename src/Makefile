PROGSFOLDER=./progs/

hike:
	bapbuild hike.plugin -pkg llvm
	bapbundle install hike.plugin

clean:
	bapbuild -clean
	dune clean
	find ./progs -type f -not -name '*.c' -not -name '*.h' -delete
	rm -rf plugins

compileO0_fizzbuzz:
	gcc -O0 -o $(PROGSFOLDER)fizzbuzz_0 $(PROGSFOLDER)fizzbuzz.c
	bap --pass=hike-convlir --hike-output fizzbuzz.ll $(PROGSFOLDER)fizzbuzz_0
	clang -O3 fizzbuzz.ll -o $(PROGSFOLDER)fizzbuzz_llvmO0

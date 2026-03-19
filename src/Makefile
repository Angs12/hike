PROGSFOLDER=./progs/

sim:
	bapbuild sim.plugin -I deobf -pkg z3 
	bapbundle install sim.plugin

llvm:
	bapbuild ppllvm.plugin -pkg z3
	bapbundle install -destdir ./plugins ppllvm.plugin

clean:
	bapbuild -clean
	dune clean
	find ./progs -type f -not -name '*.c' -not -name '*.h' -delete
	rm -rf plugins
	rm -f struct.ll
	rm -f fizzbuzz.ll
	rm -f converted.ll
	rm -f factorial.ll

test: compileO0_fizzbuzz compileO0_fact compileO0_struct 

runtest: 
	$(PROGSFOLDER)factorial_llvmO0; 
	$(PROGSFOLDER)fizzbuzz_llvmO0
	$(PROGSFOLDER)struct_llvmO0

compileO0_fizzbuzz:
	gcc -O0 -o $(PROGSFOLDER)fizzbuzz_0 $(PROGSFOLDER)fizzbuzz.c
	bap convlir -L ./plugins $(PROGSFOLDER)fizzbuzz_0 fizzbuzz.ll --optimization-level=1
	cat stdio_headers.ll fizzbuzz.ll > converted.ll
	clang -O3 -o $(PROGSFOLDER)fizzbuzz_llvmO0 converted.ll

compileO3_fizzbuzz:
	gcc -O3 -fno-pie -o $(PROGSFOLDER)fizzbuzz_3  $(PROGSFOLDER)fizzbuzz.c
	bap $(PROGSFOLDER)fizzbuzz_3 -L ./plugins --pass=ppllvm  1> fizzbuzz.ll
	clang -Oz -fno-slp-vectorize -o $(PROGSFOLDER)fizzbuzz_llvmO3 fizzbuzz.ll

compile32_O3:
	gcc -O3 -m32 -o $(PROGSFOLDER)factorial32_3  $(PROGSFOLDER)factorial.c
	bap convlir -L ./plugins $(PROGSFOLDER)factorial32_3 factorial.ll
	cat stdio_headers.ll factorial.ll > converted.ll
	clang -O3 -o $(PROGSFOLDER)factorial_llvm32O3 converted.ll

compile32_O0:
	gcc -O0 -m32 -o $(PROGSFOLDER)factorial32_0  $(PROGSFOLDER)factorial.c
	bap convlir -L ./plugins $(PROGSFOLDER)factorial32_0 factorial.ll
	cat stdio_headers.ll factorial.ll > converted.ll
	clang -O3 -o $(PROGSFOLDER)factorial_llvm32O0 converted.ll

compile32_O0_struct:
	gcc -O0 -m32 -o $(PROGSFOLDER)struct32_0  $(PROGSFOLDER)struct.c
	bap convlir -L ./plugins $(PROGSFOLDER)struct32_0 struct.ll
	cat stdio_headers.ll struct.ll > converted.ll
	clang -O3 -o $(PROGSFOLDER)struct_llvm32O0 converted.ll

compileO0_fact:
	gcc -O0 -o $(PROGSFOLDER)factorial_0  $(PROGSFOLDER)factorial.c
	bap convlir -L ./plugins $(PROGSFOLDER)factorial_0 factorial.ll --optimization-level=1
	cat stdio_headers.ll factorial.ll > converted.ll
	clang -O3 -o $(PROGSFOLDER)factorial_llvmO0 converted.ll

compileO0_struct:
	gcc -O0 -o $(PROGSFOLDER)struct_0  $(PROGSFOLDER)struct.c
	bap convlir -L ./plugins $(PROGSFOLDER)struct_0 struct.ll
	cat stdio_headers.ll struct.ll > converted.ll
	clang -O3 -o $(PROGSFOLDER)struct_llvmO0 converted.ll

compileO3_fact:
	gcc -O3 -o $(PROGSFOLDER)factorial_3  $(PROGSFOLDER)factorial.c
	bap convlir -L ./plugins $(PROGSFOLDER)factorial_3 factorial.ll
	cat stdio_headers.ll factorial.ll > converted.ll
	clang -mno-avx -O3 -fno-slp-vectorize -fno-vectorize -o $(PROGSFOLDER)factorial_llvmO3 converted.ll

compile_gcc:
	gcc -O3 -o $(PROGSFOLDER)factorial_gcc  $(PROGSFOLDER)factorial.c
	bap $(PROGSFOLDER)factorial_gcc -L ./plugins --pass=ppllvm  1> factorial.ll
	cat stdio_headers.ll factorial.ll > converted.ll
	clang -mno-avx -O3 -fno-slp-vectorize -fno-vectorize -o $(PROGSFOLDER)factorial_llvm_gcc converted.ll

compile_clang:
	clang -O3 -fpie -o $(PROGSFOLDER)factorial_clang  $(PROGSFOLDER)factorial.c
	bap $(PROGSFOLDER)factorial_clang -L ./plugins --pass=ppllvm  1> factorial.ll
	clang -O3 -o $(PROGSFOLDER)factorial_llvm_clang factorial.ll


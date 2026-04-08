PROGSFOLDER=./progs/

sim:
	bapbuild sim.plugin -I deobf -pkg z3 
	bapbundle install sim.plugin

llvm:
	bapbuild ppllvm.plugin -pkg z3 -pkg llvm 
	bapbundle install -destdir ./plugins ppllvm.plugin

clean:
	bapbuild -clean
	dune clean
	find ./progs -type f -not -name '*.c' -not -name '*.h' -delete
	rm -rf plugins

test: compileO0_fizzbuzz compileO0_fact compileO0_struct 
factorial_test: compileO0_fact compileO2_fact compileO3_fact
fizzbuzz_test: compileO0_fizzbuzz compileO2_fizzbuzz compileO3_fizzbuzz
struct_test: compileO0_struct compileO2_struct compileO3_struct

runtest: 
	$(PROGSFOLDER)factorial_llvmO0 
	$(PROGSFOLDER)fizzbuzz_llvmO0
	$(PROGSFOLDER)struct_llvmO0

runtest_factorial: 
	$(PROGSFOLDER)factorial_llvmO0;
	$(PROGSFOLDER)factorial_llvmO2 
	$(PROGSFOLDER)factorial_llvmO

runtest_fizzbuzz: 
	$(PROGSFOLDER)fizzbuzz_llvmO0 
	$(PROGSFOLDER)fizzbuzz_llvmO2 
	$(PROGSFOLDER)fizzbuzz_llvmO

runtest_struct: 
	$(PROGSFOLDER)struct_llvmO0 
	$(PROGSFOLDER)struct_llvmO2 
	$(PROGSFOLDER)struct_llvmO3

compileO0_fizzbuzz:
	gcc -O0 -o $(PROGSFOLDER)fizzbuzz_0 $(PROGSFOLDER)fizzbuzz.c
	bap convlir -L ./plugins $(PROGSFOLDER)fizzbuzz_0 fizzbuzz.ll
	clang -O3 fizzbuzz.ll -o $(PROGSFOLDER)fizzbuzz_llvmO0

compileO2_fizzbuzz:
	gcc -O2 -o $(PROGSFOLDER)fizzbuzz_2 $(PROGSFOLDER)fizzbuzz.c
	bap convlir -L ./plugins $(PROGSFOLDER)fizzbuzz_2 fizzbuzz.ll 
	cat stdio_headers.ll fizzbuzz.ll > converted.ll
	clang -O3 -o $(PROGSFOLDER)fizzbuzz_llvmO2 converted.ll

compileO3_fizzbuzz:
	gcc -O3 -o $(PROGSFOLDER)fizzbuzz_3 $(PROGSFOLDER)fizzbuzz.c
	bap convlir -L ./plugins $(PROGSFOLDER)fizzbuzz_3 fizzbuzz.ll 
	cat stdio_headers.ll fizzbuzz.ll > converted.ll
	clang -O3 -o $(PROGSFOLDER)fizzbuzz_llvmO3 converted.ll

compileO0_fact:
	gcc -O0 -o $(PROGSFOLDER)factorial_0  $(PROGSFOLDER)factorial.c
	bap convlir -L ./plugins $(PROGSFOLDER)factorial_0 factorial.ll 
	cat stdio_headers.ll factorial.ll > converted.ll
	clang -O3 -o $(PROGSFOLDER)factorial_llvmO0 converted.ll

compileO2_fact:
	gcc -O2 -o $(PROGSFOLDER)factorial_2  $(PROGSFOLDER)factorial.c
	bap convlir -L ./plugins $(PROGSFOLDER)factorial_2 factorial.ll 
	cat stdio_headers.ll factorial.ll > converted.ll
	clang -O3 -o $(PROGSFOLDER)factorial_llvmO2 converted.ll

compileO3_fact:
	gcc -O3 -o $(PROGSFOLDER)factorial_3  $(PROGSFOLDER)factorial.c
	bap convlir -L ./plugins $(PROGSFOLDER)factorial_3 factorial.ll 
	cat stdio_headers.ll factorial.ll > converted.ll
	clang -O3 -o $(PROGSFOLDER)factorial_llvmO3 converted.ll

compileO0_struct:
	gcc -O0 -o $(PROGSFOLDER)struct_0  $(PROGSFOLDER)struct.c
	bap convlir -L ./plugins $(PROGSFOLDER)struct_0 struct.ll 
	clang -O3 -o $(PROGSFOLDER)struct_llvmO0 struct.ll

compileO2_struct:
	gcc -O2 -o $(PROGSFOLDER)struct_2  $(PROGSFOLDER)struct.c
	bap convlir -L ./plugins $(PROGSFOLDER)struct_2 struct.ll
	cat stdio_headers.ll struct.ll > converted.ll
	clang -O3 -o $(PROGSFOLDER)struct_llvmO2 converted.ll

compileO3_struct:
	gcc -O3 -o $(PROGSFOLDER)struct_3  $(PROGSFOLDER)struct.c
	bap convlir -L ./plugins $(PROGSFOLDER)struct_3 struct.ll
	cat stdio_headers.ll struct.ll > converted.ll
	clang -O3 -o $(PROGSFOLDER)struct_llvmO3 converted.ll

compile_gcc:
	gcc -O3 -o $(PROGSFOLDER)factorial_gcc  $(PROGSFOLDER)factorial.c
	bap $(PROGSFOLDER)factorial_gcc -L ./plugins --pass=ppllvm  1> factorial.ll
	cat stdio_headers.ll factorial.ll > converted.ll
	clang -mno-avx -O3 -fno-slp-vectorize -fno-vectorize -o $(PROGSFOLDER)factorial_llvm_gcc converted.ll

compile_clang:
	clang -O3 -fpie -o $(PROGSFOLDER)factorial_clang  $(PROGSFOLDER)factorial.c
	bap $(PROGSFOLDER)factorial_clang -L ./plugins --pass=ppllvm  1> factorial.ll
	clang -O3 -o $(PROGSFOLDER)factorial_llvm_clang factorial.ll


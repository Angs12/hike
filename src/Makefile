sim:
	bapbuild sim.plugin -I deobf -pkg z3 
	bapbundle install sim.plugin

llvm:
	bapbuild ppllvm.plugin -pkg z3
	bapbundle install -destdir ./plugins/ ./ppllvm.plugin

clean:
	bapbuild -clean
	dune clean
	rm factorial_llvm*
	rm converted.ll
	rm factorial.ll

compileO0_fizzbuzz:
	gcc -O0 -fno-pie -o ./progs/fizzbuzz_0  ./progs/fizzbuzz.c
	bap ./progs/fizzbuzz_0 -L ./plugins --pass=ppllvm  1> fizzbuzz.ll
	clang -Oz -fno-slp-vectorize -o fizzbuzz_llvmO0 fizzbuzz.ll

compileO3_fizzbuzz:
	gcc -O3 -fno-pie -o ./progs/fizzbuzz_3  ./progs/fizzbuzz.c
	bap ./progs/fizzbuzz_3 -L ./plugins --pass=ppllvm  1> fizzbuzz.ll
	clang -Oz -fno-slp-vectorize -o fizzbuzz_llvmO3 fizzbuzz.ll

compile32:
	gcc -O0 -m32 -o ./progs/factorial32  ./progs/factorial.c
	bap ./progs/factorial32 -L ./plugins --pass=ppllvm 1> factorial.ll
	cat stdio_headers.ll factorial.ll > converted.ll
	clang -O0 -o factorial_llvm32 converted.ll

compileO0_fact:
	gcc -O0 -o ./progs/factorial_0  ./progs/factorial.c
	bap ./progs/factorial_0 -L ./plugins --pass=ppllvm  1> factorial.ll
	cat stdio_headers.ll factorial.ll > converted.ll
	clang -mno-avx -O3 -fno-slp-vectorize -fno-vectorize -o factorial_llvmO0 converted.ll 

compileO3_fact:
	gcc -O3 -o ./progs/factorial_3  ./progs/factorial.c
	bap ./progs/factorial_3 -L ./plugins --pass=ppllvm  1> factorial.ll
	clang -mno-avx -O3 -fno-slp-vectorize -fno-vectorize -o factorial_llvmO3 factorial.ll 

compile_gcc:
	gcc -O3 -o ./progs/factorial_gcc  ./progs/factorial.c
	bap ./progs/factorial_gcc -L ./plugins --pass=ppllvm  1> factorial.ll
	cat stdio_headers.ll factorial.ll > converted.ll
	clang -mno-avx -O3 -fno-slp-vectorize -fno-vectorize -o factorial_llvmO0 converted.ll 

compile_clang:
	clang -O3 -fpie -o ./progs/factorial_clang  ./progs/factorial.c
	bap ./progs/factorial_clang -L ./plugins --pass=ppllvm  1> factorial.ll
	clang -O3 -o factorial_llvm_clang factorial.ll


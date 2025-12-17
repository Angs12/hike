sim:
	bapbuild sim.plugin -I deobf -pkg z3 
	bapbundle install -destdir ./plugins/ ./sim.plugin

llvm:
	bapbuild ppllvm.plugin -I deobf -pkg z3 -pkg cbat_value_set
	bapbundle install -destdir ./plugins/ ./ppllvm.plugin

clean:
	bapbuild -build-dir ./plugins/ -clean
	rm *.plugin
	rm -rf _build

compile32:
	gcc -O0 -fno-pie -m32 -o ./progs/factorial32  ./progs/factorial.c
	bap ./progs/factorial32 -L ./plugins --pass=ppllvm 1> factorial.ll
	clang-15 -O0 -o factorial_llvm factorial.ll

compile:
	gcc -O2 -o -fno-inline-small-functions -fno-pie -o ./progs/factorial  ./progs/factorial.c
	bap ./progs/factorial -L ./plugins --pass=ppllvm  1> factorial.ll
	clang-15 -fno-inline-functions -O3 -o factorial_llvm factorial.ll


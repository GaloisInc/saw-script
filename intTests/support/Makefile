CP=.:../../deps/jvm-verifier/support/galois.jar

%.ll: %.c
	clang -S -emit-llvm $< -o $(shell basename $< .c).ll

%.bc: %.ll
	llvm-as $<

%.bc: %.c
	clang -emit-llvm -c $< -o $(shell basename $< .c).bc

%.out: %.c
	clang $< -o $(shell basename $< .c).out

%.class: %.java
	javac -cp $(CP):../jars/galois.jar $<

%.jvm-asm: %.java
	javap -c -classpath $(CP):../jars/galois.jar $(shell basename $< .java) > $@

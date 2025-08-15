all: test.bc test.linked-mir.json Test.class

test.bc: test.c
	clang -emit-llvm -c -o $@ $<

test.linked-mir.json: test.rs
	saw-rustc $<

Test.class: Test.java
	javac -g $<

clean:
	rm -f *.class *.bc *.json *.rlib *.mir test

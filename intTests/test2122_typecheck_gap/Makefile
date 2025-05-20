all: err054.bc err055.class err056.json

err054.bc: err054.c
	clang -emit-llvm -c -o $@ $<

err055.class: err055.java
	javac -g $<

err056.json: err056.rs
	saw-rustc $< && mv err056.linked-mir.json $@

clean:
	rm -f *.class *.bc *.json *.rlib *.mir err056

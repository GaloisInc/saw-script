all: test.linked-mir.json Test.class

test.linked-mir.json: test.rs
	saw-rustc $<

Test.class: Test.java
	javac -g $<

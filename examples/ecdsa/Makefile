SAW?=../../bin/saw

all : build

build : build/com/galois/ecc/ECCProvider.class

# Create Java class files
build/com/galois/ecc/ECCProvider.class :
	mkdir -p build
	javac -g -cp src src/com/galois/ecc/*.java -d build
	javac -g -cp build:tests tests/com/galois/ecc/*.java -d build

# Build Javadoc documentation.
doc :
	javadoc -classpath src -d doc -public src/com/galois/ecc/*

# Clean up generated files
clean :
	rm -rf doc build

# Run Java with 64bit data (much faster).
run64 :
	java -cp build -d64 com.galois.ecc.ECC


ecdsa.jar: build
	cd build && jar -cf ../ecdsa.jar com

# Run the SAWScript verification
verify : build
	${SAW} -c build ecdsa.saw

.PHONY : build clean doc run32 run64 verify

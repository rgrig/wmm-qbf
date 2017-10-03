all:
	./build.sh

debug:
	./build.sh byte

test: all
	./bin/Test

clean:
	ocamlbuild -clean

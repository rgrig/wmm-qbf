all:
	./build.sh

test: all
	./bin/Test

clean:
	ocamlbuild -clean

MAINS="wmmqbf wmmEnum"
TYPE="byte"

eval $(opam config env)
mkdir -p bin
for f in $MAINS; do
  ocamlbuild -use-ocamlfind $f.$TYPE
  cp $(readlink -e $f.$TYPE) bin/$f
done

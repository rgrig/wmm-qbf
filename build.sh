MAINS="Pride Test Results"
TYPE="byte"

T=""
for i in $MAINS; do
  T="$T $i.$TYPE"
done

eval $(opam config env)
ocamlbuild -use-ocamlfind $T
mkdir -p bin
for f in $MAINS; do
  cp $(readlink -e $f.$TYPE) bin/$f
done

MAINS="Pride Test ResultsBin"
TYPE="native"

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

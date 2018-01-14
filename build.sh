MAINS="Pride Test ResultsBin CatTest SoTest LISATest"

if [ -n "$1" ]; then TYPE=$1
else TYPE="native"
fi

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

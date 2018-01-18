BINARIES = LISATest Pride

$(BINARIES): all

all:
	./build.sh

debug:
	./build.sh byte

test: all
	./bin/Test

clean:
	ocamlbuild -clean

LITMUS_TESTS = data/jctc-lisa/jctc1.lisa \
  data/jctc-lisa/jctc2.lisa \
  data/jctc-lisa/jctc3.lisa \
  data/jctc-lisa/jctc4.lisa \
  data/jctc-lisa/jctc5.lisa \
  data/jctc-lisa/jctc6.lisa \
  data/jctc-lisa/jctc7.lisa \
  data/jctc-lisa/jctc8.lisa \
  data/jctc-lisa/jctc9.lisa \
  data/jctc-lisa/jctc9a.lisa \
  data/jctc-lisa/jctc10.lisa \
  data/jctc-lisa/jctc11.lisa \
  data/jctc-lisa/jctc12.lisa \
  data/jctc-lisa/jctc13.lisa \
  data/jctc-lisa/jctc14.lisa \
  data/jctc-lisa/jctc15.lisa \
  data/jctc-lisa/jctc16.lisa \
  data/jctc-lisa/jctc17.lisa \
  data/jctc-lisa/jctc18.lisa \
  data/jctc-lisa/jctc19.lisa \
  data/jctc-lisa/jctc20.lisa


%.es: %.lisa
	LISATest $< > $@ 

%.str %.sol: %.es
	Pride --solver so --dump-query --model j+r-so $<

litmusES: $(patsubst %.lisa,%.es,$(LITMUS_TESTS))
litmusQuery: $(patsubst %.lisa,%.sol,$(LITMUS_TESTS))

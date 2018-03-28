#!/bin/bash
# Generate ES and SVG files from jctc-lisa tests.

FROM_DIR="../jctc-lisa"
PRIDE_BIN="../../Pride.native"
PRIDE_ARGS="--dump-es --solver none"
SVG_BIN="../../../prideweb/bin/es_to_svg"

for path in "$FROM_DIR"/*.lisa
do
	file="$(basename $path .lisa)"
	echo "- $file -"
	cp "$FROM_DIR/$file.lisa" "$file.lisa"
	if [[ $file = *"vals-0,2"* ]]; then
		"$PRIDE_BIN" $PRIDE_ARGS --values 0,2 "$file.lisa"
	else
		"$PRIDE_BIN" $PRIDE_ARGS "$file.lisa"
	fi
	"$SVG_BIN" "$file.es" "$file.svg"
	rm "$file.lisa"
done

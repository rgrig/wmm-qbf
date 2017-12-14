#!/bin/bash

for f in `ls ../data/cat-models/*.cat`; do
    CatTest $f > $f.parsed
done

	 

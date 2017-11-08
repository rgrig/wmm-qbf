#!/bin/bash

for f in `ls ../testData/*.cat`; do
    CatTest $f > $f.parsed
done

	 

#!/usr/bin/env bash
make clean sml/time sml/time_int
parallel -j 3 -k '{} wide 20 21' ::: './sml/time SML' './sml/time_int SML' './sml/time C'
make cpp_fast=true clean sml/time sml/time_int
./sml/time C wide 20 21 

#make clean sml/time sml/time_int
#parallel -j 3 -k '{} balanced 21 25' ::: './sml/time SML' './sml/time_int SML' './sml/time C'
#make cpp_fast=true clean sml/time sml/time_int
#./sml/time C balanced 21 25

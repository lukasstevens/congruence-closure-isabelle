#!/usr/bin/env bash
make clean sml/time sml/time_int
parallel -j 3 -k '{} wide 18 22' ::: './sml/time SML' './sml/time_int SML' './sml/time C'
make cpp_fast=true clean sml/time sml/time_int
./sml/time C wide 18 22 

make clean sml/time sml/time_int
parallel -j 1 -k '{} balanced 22 26' ::: './sml/time SML' './sml/time_int SML' './sml/time C'
make cpp_fast=true clean sml/time sml/time_int
./sml/time C balanced 22 26

#!/usr/bin/env bash
make clean sml/time sml/time_int
./sml/time SML wide 20 24
./sml/time_int wide 20 24
./sml/time C wide 20 24 
make cpp_fast=true clean sml/time sml/time_int
./sml/time C wide 20 24

make clean sml/time sml/time_int
./sml/time SML balanced 21 25 
./sml/time_int balanced 21 25
./sml/time C balanced 21 25 
make cpp_fast=true clean sml/time sml/time_int
./sml/time C balanced 21 25

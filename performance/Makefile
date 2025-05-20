opt_flags ?= -O3
ostype ?= $(shell uname -s)

UFE.so: cpp/include/UFE_API.h cpp/*.cpp
	g++ "$(opt_flags)" -dynamiclib -flat_namespace cpp/UFE_C.cpp -o $@

sml/sources: sml/sources.mlb sml/*.sml UFE.so
	mlton -codegen c -cc-opt "$(opt_flags)" -default-ann 'allowFFI true' -target-link-opt $(ostype) -ldl $< 

.PHONY: clean
clean:
	rm -f UFE.so sml/sources

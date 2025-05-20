opt_flags ?= -O3
ostype ?= $(shell uname -s)
mlton_target ?= native

ifeq ($(ostype),Darwin)
	dll_flags = -dynamiclib -flat_namespace
endif
ifeq ($(ostype),Linux)
	dll_flags = -fPIC -shared
endif

UFE.so: cpp/include/UFE_API.h cpp/*.cpp
	g++ "$(opt_flags)" $(dll_flags) cpp/UFE_C.cpp -o $@

sml/sources: sml/sources.mlb sml/*.sml UFE.so
	mlton -codegen $(mlton_target) -cc-opt "$(opt_flags)" -default-ann 'allowFFI true' -target-link-opt $(ostype) -ldl $< 

.PHONY: clean
clean:
	rm -f UFE.so sml/sources

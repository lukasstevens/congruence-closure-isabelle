opt_flags ?= -O3
ostype ?= $(shell uname -s)
debug ?= false
ml_profile ?= false
cpp_fast ?= false

ifeq ($(ostype),Darwin)
	mlton_codegen = -codegen c 
	dll_flags = -dynamiclib -flat_namespace
endif
ifeq ($(ostype),Linux)
	mlton_codegen = -codegen native 
	dll_flags = -fPIC -shared
endif

ifeq ($(ml_profile),true)
	ml_profile_flags += -profile time
endif

ifeq ($(debug),true)
	ccp_cc += -g
endif

ifeq ($(cpp_fast),true)	
	cpp_cc += -DCPP_FAST
endif

cpp_cc = g++ $(opt_flags)
ml_cc = mlton -cc-opt "$(opt_flags)" $(mlton_codegen) -default-ann 'allowFFI true' -target-link-opt $(ostype) 

cpp_test.out: cpp/UFE.cpp cpp/test/Test.cpp
	$(cpp_cc) cpp/test/Test.cpp -o $@

.PHONY: cpp_test
cpp_test: cpp_test.out
	./$<

UFE.so: cpp/include/UFE_API.h cpp/*.cpp
	$(cpp_cc) $(dll_flags) cpp/UFE_C.cpp -o $@

sml/time: sml/time.mlb sml/*.sml UFE.so
	$(ml_cc) -ldl $< 

sml/time_int: sml/time_int.mlb sml/*.sml UFE.so
	$(ml_cc) -ldl $< 

.PHONY: clean
clean:
	rm -f UFE.so sml/time sml/time_int

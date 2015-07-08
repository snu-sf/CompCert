all: __i64_dtos extern_pointer_const

__i64_dtos: __i64_dtos.c
	ccomp -dasm -o __i64_dtos __i64_dtos.c

extern_pointer_const: extern_pointer_const_a.c extern_pointer_const_b.c
	ccomp -dasm -o extern_pointer_const extern_pointer_const_a.c extern_pointer_const_b.c

clean:
	rm -rf *.s *.o __i64_dtos extern_pointer_const

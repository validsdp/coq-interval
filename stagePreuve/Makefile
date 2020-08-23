COQ=coqc

all: r2Preuve.vos

r2Preuve.vos: r2Preuve.v libs
	coqc $<

libs: r2Defs.vos r2Generic.vos

r2Generic.vos: r2Generic.v r2Defs.vos
	coqc $<

r2Defs.vos: r2Defs.v
	coqc $<

.PHONY: clean
clean:
	rm -f *.vo*
	rm -f .*.aux
	rm -f *.glob
	rm -f .*.cache
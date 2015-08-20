JRWTactics.vo: JRWTactics.v
	coqc JRWTactics.v

.PHONY: clean

clean:
	rm -f *.vo *.glob *.aux *~

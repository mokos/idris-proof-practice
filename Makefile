# usage example: make nat
%: %.idr
	idris $*.idr -o $*
	rm $*.ibc

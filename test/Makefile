##  Makefile

IDRIS := idris
OPTS  := -p effects -p protocols


util:
	${IDRIS} ${OPTS} UtilServer.idr -o util

stream:
	${IDRIS} ${OPTS} Stream.idr -o stream

knock:
	${IDRIS} ${OPTS} Knock.idr -o knock

shake:
	${IDRIS} ${OPTS} TCP.idr -o shake

fail:
	${IDRIS} ${OPTS} --nocolor TCPFail.idr -o shakefail

working: clean util stream knock shake


clean:
	rm -f *.ibc util stream knock shake output

.PHONY: clean util stream knock shake fail

##  Makefile

IDRIS := idris
PKG   := protocols
OPTS  :=

install: clean
	${IDRIS} ${OPTS} --install ${PKG}.ipkg

build: clean
	${IDRIS} ${OPTS} --build ${PKG}.ipkg

clean:
	${IDRIS} --clean ${PKG}.ipkg
	find . -name "*~" -delete

check: clean
	${IDRIS} --checkpkg ${PKG}.ipkg

doc:
	${IDRIS} --makedoc ${PKG}.ipkg

test: install
	(cd test; sh runtests.sh ${IDRIS})


.PHONY: clean

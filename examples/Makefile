AGDA_EXEC?=agda-2.8.0
BUILDDIR=_build/


all:
	mkdir -p $(BUILDDIR)
	$(AGDA_EXEC) -c Main.agda --ghc-dont-call-ghc --compile-dir=$(BUILDDIR)
	cabal build
	cabal run

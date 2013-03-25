CABAL-CONFIGURE-FLAGS 	:= --user
CABAL-BUILD-FLAGS     	:=
VERSION					:= 0.0.5

AG						:= src/CCO/Imp/AG.ag src/CCO/Imp/AG/Base.ag src/CCO/Imp/AG/CodeGeneration.ag

all : haskell

src/CCO/Imp/AG.hs : $(AG)
	uuagc -Hdcfws --self -P src/CCO/Imp src/CCO/Imp/AG.ag

haskell : src/CCO/Imp/AG.hs
	runhaskell Setup.lhs configure $(CABAL-CONFIGURE-FLAGS)
	runhaskell Setup.lhs build $(CABAL-BUILD-FLAGS)

dist:
	tar tfz imp-$(VERSION).tar.gz $(AG)

.PHONY : haskell dist

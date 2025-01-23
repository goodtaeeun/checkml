MAKE=@make
DUNE=@dune
LN=@ln -sf
RM=@rm
EXE=checkml

all:
	$(DUNE) build src/main.exe
	$(LN) _build/default/src/main.exe $(EXE)

test: all
	$(DUNE) test

promote: all
	$(DUNE) promote

clean:
	$(DUNE) clean
	$(RM) -rf $(EXE)

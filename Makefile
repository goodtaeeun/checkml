MAKE=@make
DUNE=@dune
LN=@ln -sf
RM=@rm
EXE=checkml

all:
	
ifndef GITHUB_CI
	$(DUNE) build
	$(LN) _build/default/src/checkml.exe $(EXE)
else
	$(DUNE) install


test: all
	$(DUNE) test

promote:
	$(DUNE) promote

clean:
	$(DUNE) clean
	$(RM) -rf $(EXE)

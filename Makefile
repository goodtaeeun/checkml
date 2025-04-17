MAKE=@make
DUNE=@dune
LN=@ln -sf
RM=@rm
EXE=checkml

all:
	$(DUNE) build --build-dir=./temp_build
ifndef GITHUB_CI
	$(LN) _build/default/src/checkml.exe $(EXE)
endif

test: all
	$(DUNE) test

promote:
	$(DUNE) promote

clean:
	$(DUNE) clean
	$(RM) -rf $(EXE)

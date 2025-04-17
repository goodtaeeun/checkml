MAKE=@make
DUNE=@dune
LN=@ln -sf
RM=@rm
EXE=checkml

all:
	$(DUNE) build --build-dir=./temp_build

test: all
	$(DUNE) test

promote:
	$(DUNE) promote

clean:
	$(DUNE) clean
	$(RM) -rf $(EXE)

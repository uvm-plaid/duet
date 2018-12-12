NAME := duet

.PHONY: run
run: $(NAME).cabal
	stack run

.PHONY: interact
interact: $(NAME).cabal
	stack ghci $(NAME)

.PHONY: build
build: $(NAME).cabal
	stack build

.PHONY: build-profile
build-profile: $(NAME).cabal
	stack build --profile

.PHONY: install
install: $(NAME).cabal
	stack install

.PHONY: configure
configure: $(NAME).cabal

.PHONY: doc
doc:
	stack haddock
	cp -r `stack path --local-doc-root` ./

$(NAME).cabal: package.yaml
	hpack --force

.PHONY: clean
clean:
	stack clean
	rm -f $(NAME).cabal



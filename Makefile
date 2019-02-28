NAME := duet
ARGS := lr-accuracy data_long/adp1kxs.csv data_long/adp1kys.csv out/out.csv

# run examples/gd-pb.ed.duet data_long/adp1kxs.csv data_long/adp1kys.csv 0.05 100 0.0001 0.0001 1

# stack ghci
# :set args check "examples/gd-pb.ed.duet"
# main

.PHONY: run
run: $(NAME).cabal
	stack run -- $(ARGS)

.PHONY: run-profile
run-profile: $(NAME).cabal
	stack run --profile -- $(ARGS)

.PHONY: interact
interact: $(NAME).cabal
	stack ghci $(NAME)

.PHONY: build
build: $(NAME).cabal
	stack build --fast

.PHONY: build-profile
build-profile: $(NAME).cabal
	stack build --profile

.PHONY: install
install: $(NAME).cabal
	stack install

.PHONY: configure
configure: $(NAME).cabal

# .PHONY: doc
# doc:
# 	stack haddock
# 	cp -r `stack path --local-doc-root` ./

.PHONY: clean
clean:
	stack clean --full
	rm -f $(NAME).cabal
	rm -rf doc

# .PHONY: hoogle
# hoogle:
# 	stack hoogle -- generate --local
# 	(sleep 1 && open http://localhost:8080/?scope=package%3A$(NAME)) &
# 	stack hoogle -- server --local --port=8080

$(NAME).cabal: package.yaml
	hpack --force

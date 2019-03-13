NAME := duet

ARGS := check examples/gd-pb.ed.duet
ARGS := run examples/gd-pb.ed.duet data_short/fbxs.csv data_short/fbys.csv 0.05 100 0.0001 0.0001 1
ARGS := run examples/presna-crisis.eps.duet data_short/incoming.csv data_short/outgoing.csv 1.0

# Working Examples
# run examples/gd-pb-mini.ed.duet data_long/adp1kxs.csv data_long/adp1kys.csv 0.05 100 0.0001 0.0001 1 50
# run examples/gd-pb-mini.ed.duet data_short/fbxs.csv data_short/fbys.csv 0.05 100 0.0001 0.0001 1 50
# run examples/parallel-simple.ed.duet data_short/made_up.csv 0.05 0.0001 0 0 0 1
# run examples/basic-boxing.ed.duet 1
# run examples/baby.ed.duet 0.05 0.0001 data_short/made_up.csv
# lr-accuracy data_long/adp1kxs.csv data_long/adp1kys.csv out/out.csv

# Run Using GHCI
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

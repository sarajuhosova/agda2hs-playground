run: compile
	@cabal run

build: compile
	@echo "Building the Haskell project..."
	@cabal build
	@echo ""

compile:
	@echo "Generating Haskell library with Agda2HS..."
	@chmod +x build.sh
	@./build.sh
	@echo ""

install :
	@cabal new-install --overwrite-policy=always

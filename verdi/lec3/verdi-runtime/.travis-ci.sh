set -ev

opam init --yes --no-setup
eval $(opam config env)

opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net

opam pin add verdi-runtime . --yes --verbose

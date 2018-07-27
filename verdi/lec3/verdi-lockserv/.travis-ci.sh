set -ev

opam init --yes --no-setup
eval $(opam config env)

opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net

opam pin add coq $COQ_VERSION --yes --verbose

case $MODE in
  lockserv)
    opam pin add lockserv . --yes --verbose
    ;;
  lockserv-seqnum)
    opam pin add lockserv-seqnum . --yes --verbose
    ;;
  lockserv-serialized)
    opam pin add lockserv-serialized . --yes --verbose
    ;;
  *)
    opam pin add verdi-lockserv . --yes --verbose
    ;;
esac

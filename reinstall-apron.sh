#!/bin/bash

opam remove apron -y
opam pin add apron . -n --yes
opam install -j 30 apron --yes 

notify-send -u critical "Done reinstalling APRON"

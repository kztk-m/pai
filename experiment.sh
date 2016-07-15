#!/bin/sh
for i in snoc zip dbl rl #snoc dl tl rl rev b2p p2b sb print_sexp zip dbl
do
    echo "============================"
    echo " $i "
    echo "============================"
    for j in 1 1 1 0 0 0
    do
    ./Experiment $i $j +RTS -K512M -H768M
    echo ""
    done 
    echo "\n\n"
done
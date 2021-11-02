#!/usr/bin/env zsh

echo c,k,m,cs
for c in jubjub vellas pasta
do
    for k in 100 300 1000 3000 10000
    do
        for m in 10 20 30 40
        do
            cs=$(cargo run --release --example measure_constraints $k $m -c $c)
            echo $c,$k,$m,$cs
        done
    done
done

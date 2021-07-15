#!/usr/bin/env zsh

echo k,m,cs
for k in 100 300 1000 3000 10000
do
    for m in 10 20 30 40
    do
        cs=$(cargo run --release --example measure_constraints $k $m)
        echo $k,$m,$cs
    done
done

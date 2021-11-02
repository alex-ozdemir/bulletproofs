#!/usr/bin/env zsh

echo k,m,cs
for k in $(seq 6 6 144)
do
    for m in $(seq 2 2 20)
    do
        cs=$(cargo run --release --example measure_constraints $k $m -c pasta)
        echo $k,$m,$cs
    done
done

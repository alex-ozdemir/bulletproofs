#!/usr/bin/env zsh

set -e
repo_root=$(git rev-parse --show-toplevel)

cargo build --release --example llbp

bin="${repo_root}/target/release/examples/llbp"

# maps from log2n, made automatically
declare -A ks
ks=(
  1 6
  2 6
  3 6
  4 6
  5 7
  6 6
  7 6
  8 10
  9 6
  10 7
  11 15
  12 27
  13 10
  14 13
  15 18
  16 10
  17 12
  18 16
  19 31
  20 12
  21 15
  22 22
  23 27
  24 36
  25 18
  26 22
  27 26
  28 32
  29 18
  30 21
)
declare -A rs
rs=(
  1 1
  2 1
  3 1
  4 1
  5 1
  6 2
  7 2
  8 2
  9 3
  10 3
  11 2
  12 2
  13 3
  14 3
  15 3
  16 4
  17 4
  18 4
  19 3
  20 5
  21 5
  22 4
  23 4
  24 4
  25 5
  26 5
  27 5
  28 5
  29 6
  30 6
)

echo pf,log2n,n,trial,pf_wall_time,pf_size,ver_wall_time
trials=3
max_log2n=11
for t in $(seq 1 $trials)
do
    for log2n in $(seq 5 $max_log2n)
    do
        n=$((2 ** $log2n))
        k=${ks[$log2n]}
        r=${rs[$log2n]}

        # bp
        output=$(RUST_LOG='pf_time=debug,pf_size=debug,ver_time=debug' $bin -p bp $n 0 0 2>&1)
        pf_wall_time=$(echo $output | rg "Proof time " | rg -o '[0-9.]+$')
        pf_size=$(echo $output | rg "Proof size" | rg -o '[0-9.]+$')
        ver_wall_time=$(echo $output | rg "Verifier time " | rg -o '[0-9.]+$')
        echo bp,$log2n,$n,$t,$pf_wall_time,$pf_size,$ver_wall_time

        # llbp
        output=$(RUST_LOG='pf_time=debug,pf_size=debug,ver_time=debug' $bin -p llbp $n $k $r 2>&1)
        pf_wall_time=$(echo $output | rg "Proof time " | rg -o '[0-9.]+$')
        pf_size=$(echo $output | rg "Proof size" | rg -o '[0-9.]+$')
        ver_wall_time=$(echo $output | rg "Verifier time " | rg -o '[0-9.]+$')
        echo llbp,$log2n,$n,$t,$pf_wall_time,$pf_size,$ver_wall_time
    done
done

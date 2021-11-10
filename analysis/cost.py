#!/usr/bin/env python3

from typing import NamedTuple
from math import ceil, log
import argparse as arg
import sys


class ConstraintCostModel(NamedTuple):
    constant: float
    # coefficients:
    # l: fixed-scalar MSM size
    # l /log2 l
    l_by_log2l: float
    # l
    l: float
    # m: IP size
    m: float

    def cs_continuous(self, l, m):
        return self.l_by_log2l * l / log(l, 2) + self.m * m + self.constant + self.l * l


class CircuitPrimitiveCosts(NamedTuple):
    # assuming ~ n / log n
    fs_msm_adds_25000_elems: float
    fb_msm_cs_per_bit: float
    cs_per_nonnative_ip_elem: float
    cs_per_nonnative_ip_reduce: float
    cs_per_op: float

    def to_cs_cost_model(self):
        lam = 128
        field_bits = 2 * lam
        bit_check = 1
        per_m = (
            2 * (self.fb_msm_cs_per_bit + bit_check) * field_bits
            + self.cs_per_nonnative_ip_elem
        )

        return ConstraintCostModel(
            self.cs_per_nonnative_ip_reduce,
            float(
                self.fs_msm_adds_25000_elems * self.cs_per_op / 25000 * log(25000, 2)
            ),
            0.0,
            per_m,
        )


class LLBPConfig(NamedTuple):
    N: int
    k: int
    r: int
    model: ConstraintCostModel

    def cs(self):
        fs_msm_size = 2 * (self.k - 1) * self.r + 1
        ip_size = ceil(self.N / self.k ** self.r)
        return self.model.cs_continuous(fs_msm_size, ip_size)

    def proof_size(self):
        inner_ip_size = 2 * self.cs()
        return 1 + self.r + 2 * ceil(log(inner_ip_size, 2)) + 2

    def cs_continuous_apx(self):
        fs_msm_size = 2 * (self.k - 1) * self.r + 1
        ip_size = float(self.N / self.k ** self.r)
        return self.model.cs_continuous(fs_msm_size, ip_size)

    def proof_size_continuous_apx(self):
        inner_ip_size = 2 * self.cs()
        return 1 + self.r + 2 * log(inner_ip_size, 2) + 2


model = ConstraintCostModel(1765.4, 1288, -0.6, 1800.8)

p = arg.ArgumentParser()
p.add_argument(
    "-o",
    "--output",
    choices=["debug", "zsh", "table"],
    default="debug",
    help="The kind of output to yeild",
)
args = p.parse_args()

if args.output == "debug":
    for log2N in range(1, 31):
        N = 2 ** log2N
        options = sorted(
            sorted(
                [
                    (
                        log2N,
                        N,
                        r,
                        k,
                        LLBPConfig(N, k, r, model).proof_size_continuous_apx(),
                        LLBPConfig(N, k, r, model).proof_size(),
                        log2N * 2 + 2,
                    )
                    for k in range(6, 40)
                    for r in range(1, 7)
                ]
            ),
            key=lambda p: (p[5], p[4]),
        )
        print(options[0])
elif args.output == "zsh":
    print("declare -A ks\nks=(")
    for log2N in range(1, 31):
        N = 2 ** log2N
        options = sorted(
            sorted(
                [
                    (
                        log2N,
                        N,
                        r,
                        k,
                        LLBPConfig(N, k, r, model).proof_size(),
                        log2N * 2 + 2,
                    )
                    for k in range(6, 40)
                    for r in range(1, 7)
                ]
            ),
            key=lambda p: p[4],
        )
        k = options[0][3]
        r = options[0][2]
        print(f"  {log2N} {k}")
    print(")")
    print("declare -A rs\nrs=(")
    for log2N in range(1, 31):
        N = 2 ** log2N
        options = sorted(
            sorted(
                [
                    (
                        log2N,
                        N,
                        r,
                        k,
                        LLBPConfig(N, k, r, model).proof_size(),
                        log2N * 2 + 2,
                    )
                    for k in range(6, 40)
                    for r in range(1, 7)
                ]
            ),
            key=lambda p: p[4],
        )
        k = options[0][3]
        r = options[0][2]
        print(f"  {log2N} {r}")
    print(")")
elif args.output == "table":
    N_R = 7
    N_N = 30
    m = {}
    for log2N in range(1, N_N + 1):
        N = 2 ** log2N
        for r in range(1, N_R + 1):
            m[(log2N, r)] = sorted(
                [
                    (
                        log2N,
                        N,
                        r,
                        k,
                        LLBPConfig(N, k, r, model).proof_size_continuous_apx(),
                        LLBPConfig(N, k, r, model).proof_size(),
                        log2N * 2 + 2,
                    )
                    for k in range(6, 40)
                ],
                key=lambda p: (p[5], p[4]),
            )[0]

    print(r"\begin{tabular}{ll" + "r"*r + r"}\toprule")
    print(r"$\log_2N$ & BP", end='')
    for r in range(1, N_R + 1):
        print(end=f' & $r={r}$')
    print(r"\\\midrule")
    for log2N in range(15, N_N + 1):
        N = 2 ** log2N
        print(f" {{$\\begin{{aligned}}{log2N}\\\\-\\end{{aligned}}$}}")
        print(f" & {{$\\begin{{aligned}}|\\pi|&={2*log2N+2}\\\\-\\end{{aligned}}$}}")
        for r in range(1, N_R + 1):
            #print(f" & $|\\pi|={m[(log2N, r)][5]}$")
            size = m[(log2N, r)][5]
            k = m[(log2N, r)][3]
            if size <= min( m[(log2N, r)][5] for r in range(1, N_R+1)):
                print(f" & {{$\\begin{{aligned}}|\\pi|&=\\bm{{\\textcolor{{ForestGreen}}{{ {size} }} }}\\\\ k&={k} \\end{{aligned}}$}}")
            else:
                print(f" & {{$\\begin{{aligned}}|\\pi|&={size}\\\\ k&={k} \\end{{aligned}}$}}")
        print(r"\\")
        #print(" & ")
        #for r in range(1, N_R + 1):
        #    print(f" & $k={m[(log2N, r)][3]}$")
        #print(r"\\")
    print(r"\end{tabular}")

else:
    print("Bad output: ", args.output)
    sys.exit(2)

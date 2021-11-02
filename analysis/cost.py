#!/usr/bin/env python3

from typing import NamedTuple
from math import ceil, log


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

    def inner_ip_size(self):
        cs = self.cs()
        return 2 * cs

    def proof_size(self):
        inner_ip_size = 2 * self.cs()
        return 1 + self.r + 2 * ceil(log(inner_ip_size, 2)) + 2


model = ConstraintCostModel(1765.4, 1288, -0.6, 1800.8)

for log2N in range(1, 31):
    N = 2 ** log2N
    options = sorted(
        sorted(
            [
                (log2N, N, r, k, LLBPConfig(N, k, r, model).proof_size(), log2N*2+2)
                for k in range(6, 40)
                for r in range(1, 7)
            ]
        ),
        key=lambda p: p[4],
    )
    print(options[0])

#!/usr/bin/env python

from math import log2, ceil

fb_msm_per_bit = 3.2
lam = 128
f_bits = 2 * 128


def fs_msm_per_elem(n):
    return 1800 / log2(n)  # from experiments


nn_f_prod_no_red = 9
nn_f_prod_red = 1.3 * f_bits
print(fs_msm_per_elem(1000))
print(fs_msm_per_elem(10000))


def cs_bp_rec(n, r):
    k = n ** (1 / (r + 1))
    m = n / k ** r
    fs_msm = fs_msm_per_elem(k * r) * k * r
    bp_com = 2 * m * (fb_msm_per_bit + 1) * f_bits
    msg_combine = r * k
    msg_compress = k * (f_bits * 2 + 4)
    msg_com = k * fb_msm_per_bit * f_bits + msg_compress + msg_combine
    return fs_msm + bp_com + msg_com


def bp_size(n):
    return 2 * int(ceil(log2(n)))


def rec_size(n, r):
    return r + int(ceil(bp_size(cs_bp_rec(n, r))))


def print_table(size_fn):
    r_range = list(range(1, 11, 1))
    print(
        f"{'n':4} {'bp':4} "
        + " ".join("{:>6}".format(f"r={i}") for i in r_range)
        + "   best"
        + " shrink"
    )
    for nlog2 in range(10, 31):
        n = 2 ** nlog2
        line = f"n^{nlog2:2} {bp_size(n):4}"
        sizes = []
        for r in r_range:
            w_rec = size_fn(n, r)
            sizes.append(w_rec)
            line += f" {w_rec:6d}"
        best = min(sizes)
        shrink = bp_size(n) / best
        line += f" {best:6d}"
        line += f" {shrink:6.3f}"
        print(line)


def cs_bp_rec_com_integrate(n, r):
    k = n ** (1 / (r + 1))
    m = n / k ** r

    assert 0.9 < m * k ** r / n < 1.1
    fs_msm = fs_msm_per_elem(k * r) * k * r
    bp_com = 2 * m * (fb_msm_per_bit + 1) * f_bits
    cs = fs_msm + bp_com
    com = k
    return max(com, cs)


def rec_size_com_integrate(n, r):
    return r + int(ceil(bp_size(cs_bp_rec_com_integrate(n, r))))


print("Direct")
print_table(rec_size)
print("With commitment integration")
print_table(rec_size_com_integrate)

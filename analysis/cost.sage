from typing import NamedTuple


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

    def mk_func(self, l, m):
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


# from measurement
# jubjub/bls12_381_g1
# actual_cs_costs = ConstraintCostModel(1941.2, 1927.5, -8.2, 2622.5)
# pasta
actual_cs_costs = ConstraintCostModel(1751.7, 1299, -1.7, 1799)

# pasta, ark
pasta_prims = CircuitPrimitiveCosts(
    fs_msm_adds_25000_elems=21 * 25000,  # can do better?
    fb_msm_cs_per_bit=2.333,  # zcash
    cs_per_nonnative_ip_elem=100,  # karatsuba, 3 limbs
    cs_per_nonnative_ip_reduce=actual_cs_costs.constant,  # idk
    cs_per_op=4,
)
# theoretical
best_prims = CircuitPrimitiveCosts(
    fs_msm_adds_25000_elems=21 * 25000,  # can do better?
    fb_msm_cs_per_bit=3.2,  # zcash
    cs_per_nonnative_ip_elem=6,  # karatsuba, 3 limbs
    cs_per_nonnative_ip_reduce=actual_cs_costs.constant,  # idk
    cs_per_op=6,
)
ark_prims = CircuitPrimitiveCosts(
    fs_msm_adds_25000_elems=21 * 25000,
    fb_msm_cs_per_bit=4,  # no windows?
    cs_per_nonnative_ip_elem=100,  # too many limbs?
    cs_per_nonnative_ip_reduce=actual_cs_costs.constant,
    cs_per_op=6,
)

theory_cs_costs = pasta_prims.to_cs_cost_model()


def constraints(k, r, n, cs_costs: ConstraintCostModel):
    fs_msm_size = (k - 1) * r + 1
    ip_width = n / k ^ r
    return cs_costs.mk_func(fs_msm_size, ip_width)


def pf_size(k, r, n, cs_costs: ConstraintCostModel):
    ipa_elements = constraints(k, r, n, cs_costs) + k
    return (
        r
        + 1  # commitments at each unroll
        + bp_pf_size(ipa_elements)  # r1cs->IPA compiler  # BP for the IPA
    )


def bp_pf_size(n):
    return 2 * log(n, 2) + 2


vars = var("l m k r n")
theory_size = pf_size(k, r, n, theory_cs_costs)
actual_size = pf_size(k, r, n, actual_cs_costs)
baseline_size = bp_pf_size(n)


print("l: fixed-scalar MSM size; m: IP size")
print("Cs costs theory   :", theory_cs_costs.mk_func(l, m))
print("Cs costs impl     :", actual_cs_costs.mk_func(l, m))
# print("theory,  given ark:", ark_prims.to_cs_cost_model().mk_func(l, m))


def print_size_table(size_fn):
    r_vals = list(range(1, 7))

    bigger_rs_needed = True
    while bigger_rs_needed:
        bigger_rs_needed = False
        line = ["{:6}".format("n"), f"{'bp':>6}"]
        for r_val in r_vals:
            line.append("{:>6}".format(f"r={r_val}"))
        line.append("{:11}".format("size change"))
        print("Proof size, in group elements")
        print(
            "n: IPA size, r: # of pre-SNARK rounds, k (branching factor) is optimized"
        )
        print(" ".join(line))
        for log2n in range(5, 31):
            n_val = float(2 ^ log2n)
            line = ["{:6}".format(f"2^{log2n}")]
            bp_size = float(baseline_size(n=n_val))
            line.append(f"{bp_size:6.1f}")
            sizes = []
            for r_val in r_vals:
                residual_fn = size_fn(r=r_val, n=n_val)
                # doesn't account for log factor or constant ratio
                k_guess = float(n_val ^ (1 / (r_val + 1)))
                k_best = minimize(residual_fn, [k_guess], verbose=False)[0]
                if k_best > 0:
                    size = float(residual_fn(k=k_best))
                    line.append(f"{size:>6.1f}")
                    sizes.append(size)
                else:
                    line.append(f"{'ERR':>6}")
            best_size = min(sizes)
            change = (best_size - bp_size) / bp_size
            line.append(f"{change:11.0%}")
            r_val = sizes.index(best_size) + 1
            best_residual_fn = size_fn(r=r_val, n=n_val)
            best_k_guess = float(n_val ^ (1 / (r_val + 1)))
            best_k_best = minimize(best_residual_fn, [best_k_guess], verbose=False)[0]
            line.append(f" k={best_k_best}")
            print(" ".join(line))
            if sizes[-1] < sizes[-2]:
                r_vals.append(r_vals[-1] + 1)
                print("need to try bigger r values")
                bigger_rs_needed = True


# print_size_table(actual_size)
print_size_table(theory_size)

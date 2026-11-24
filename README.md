# Kisielewicz's formula for the Dedekind numbers, in Lean 4

The Dedekind number `M(n)` counts the monotone Boolean functions of `n` variables. Kisielewicz (1988) wrote it as a
finite sum of products of binary digits:

$$M(n)=\sum_{k=1}^{2^{2^n}}\ \prod_{j=1}^{2^n-1}\ \prod_{i=0}^{j-1}\left(1-b_i^k b_j^k\prod_{m=0}^{\log_2 i}\left(1-b_m^i+b_m^i b_m^j\right)\right),$$

where $b_i^k$ is the $i$-th binary digit of $k$. This project proves it for every `n`.

| Theorem | Statement |
|---|---|
| `DedekindNumber.M_eq_kisielewiczFormula` | the formula as [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) states it, with `k` from `0` to `2^(2^n) - 1` and natural-number arithmetic |
| `DedekindNumber.M_eq_sum_bit` | the formula as printed above, over the integers, with digits given by the floor function |

Both use only the axioms `propext`, `Classical.choice` and `Quot.sound`.

Registered in Palomar as [PALOMAR-2026-11-24-000019](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-24-000019)
(commit `acdab46a`, Lean and Mathlib 4.35.0).

## The proof

Read `k` as a family of subsets of an `n`-element set: the subset whose elements are the positions of the digits `1` of
`i` belongs to the family when the `i`-th digit of `k` is `1`. The innermost product is `1` when the subset coded by `i` is
contained in the subset coded by `j`, and `0` otherwise. Containment forces `i ≤ j`, so only pairs `i < j` matter: the term
of `k` is `1` when the family is an antichain and `0` otherwise. The sum counts antichains, and there are as many of them
as monotone Boolean functions.

## What it does not do

The formula is an identity, not a practical algorithm: the sum has `2^(2^n)` terms. No Dedekind number is computed here, and
`M(10)` stays unknown. The mathematics is Kisielewicz's; only the formalization is new, as far as we could find.

## Files

| Path | What |
|---|---|
| `Challenge.lean` | the two statements, with the definitions they use |
| `Solution.lean` | the same statements, proved |
| `KisielewiczDedekind/Defs.lean` | definitions, copied from Formal Conjectures with the proof that antichains and monotone functions are equinumerous |
| `KisielewiczDedekind/Proof.lean` | the proof of the formula |

## Build

```sh
lake exe cache get
lake build
```

## Credits and license

The definitions, the statement `M_eq_kisielewiczFormula` and the proof of `M_eq_M'` come from Formal Conjectures
(Apache License 2.0). The rest was written with Claude Code (Claude Opus 5.5); `formalization.yaml` gives the details.
License: Apache 2.0.

A. Kisielewicz, *A solution of Dedekind's problem on the number of isotone Boolean functions*, J. reine angew. Math. 386
(1988), 139–144, [doi:10.1515/crll.1988.386.139](https://doi.org/10.1515/crll.1988.386.139).

/-
Copyright 2025 The Formal Conjectures Authors.
Copyright 2026 Joel Cruz Cabrera.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib

/-!
# Kisielewicz's formula for the Dedekind numbers

The Dedekind number `M n` is the number of monotone Boolean functions of `n` variables. Kisielewicz
(1988) wrote it as a finite sum of products of binary digits. The definitions `piFinBoolDecidableLE`, `M`
and `kisielewiczFormula` and the statement `M_eq_kisielewiczFormula` are copied from
`FormalConjectures/Wikipedia/DedekindNumber.lean` of google-deepmind/formal-conjectures, with their
bodies unchanged. `M_eq_sum_bit` states the formula a second time, over the integers and with the ranges
usually printed.

The formula is an identity, not a fast algorithm: the sum has `2 ^ 2 ^ n` terms. Nothing here computes a
new Dedekind number.

*References:*
- A. Kisielewicz, *A solution of Dedekind's problem on the number of isotone Boolean functions*,
  J. reine angew. Math. 386 (1988), 139–144.
- https://en.wikipedia.org/wiki/Dedekind_number#Summation_formula
-/

@[expose] public section

namespace DedekindNumber

open Finset

/-- The pointwise order on Boolean vectors is decidable. -/
instance piFinBoolDecidableLE {n : ℕ} :
    DecidableRel (fun (a b : Fin n → Bool) => a ≤ b) :=
  fun a b => show Decidable (a ≤ b) from by
    rw [Pi.le_def]
    exact Fintype.decidableForallFintype

/-- $M(n)$ is the number of monotone Boolean functions on $n$ variables. -/
def M (n : ℕ) : ℕ :=
  Fintype.card {f : (Fin n → Bool) → Bool // Monotone f}

/-- Kisielewicz's sum, as a natural number, exactly as Formal Conjectures writes it. The number `k` runs
over `0, …, 2 ^ 2 ^ n - 1`, and `i.testBit m` is the `m`-th binary digit of `i`. Every subtraction takes
a number that is `0` or `1` away from `1`, so truncation plays no role. -/
def kisielewiczFormula (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 ^ (2 ^ n)), ∏ j ∈ Finset.Icc 1 (2 ^ n), ∏ i ∈ Finset.range j,
    (1 - (k.testBit i).toNat * (k.testBit j).toNat * ∏ m ∈ Finset.range (i.log2 + 1),
      (1 - (i.testBit m).toNat + (i.testBit m).toNat * (j.testBit m).toNat))

/-- The `i`-th binary digit of `k`, as the integer `⌊k / 2 ^ i⌋ - 2 ⌊k / 2 ^ (i + 1)⌋`. -/
def bit (k i : ℕ) : ℤ := (k / 2 ^ i : ℕ) - 2 * (k / 2 ^ (i + 1) : ℕ)

/-- **Kisielewicz's formula.** The number of monotone Boolean functions of `n` variables is given by
Kisielewicz's sum. This is `DedekindNumber.M_eq_kisielewiczFormula` of Formal Conjectures. -/
theorem M_eq_kisielewiczFormula : M = kisielewiczFormula := by
  sorry

/-- **Kisielewicz's formula**, with integer arithmetic, floor-function digits and the ranges usually
printed: `k` from `1` to `2 ^ 2 ^ n`, `j` from `1` to `2 ^ n - 1` and `i` from `0` to `j - 1`. The
upper limit `log₂ i` of the last product is `0` when `i = 0`. -/
theorem M_eq_sum_bit (n : ℕ) :
    (M n : ℤ) = ∑ k ∈ Icc 1 (2 ^ 2 ^ n), ∏ j ∈ Icc 1 (2 ^ n - 1), ∏ i ∈ range j,
      (1 - bit k i * bit k j * ∏ m ∈ range (i.log2 + 1), (1 - bit i m + bit i m * bit j m)) := by
  sorry

end DedekindNumber

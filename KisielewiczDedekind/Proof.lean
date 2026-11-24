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

public import KisielewiczDedekind.Defs

/-!
# Proof of Kisielewicz's formula

A number `k < 2 ^ 2 ^ n` is read as a family of subsets of `Fin n`: the subset whose elements are the
positions of the digits `1` of `i` belongs to the family when the `i`-th digit of `k` is `1`. The
innermost product is `1` when the first subset is contained in the second and `0` otherwise. Containment
forces `i ≤ j`, so it is enough to look at the pairs `i < j`: the term of `k` is `1` when the family is
an antichain and `0` otherwise, and the sum counts antichains.
-/

@[expose] public section

namespace DedekindNumber

open Finset

/-- A number below `2 ^ n` read as a set of bit positions. -/
def bitSet (n k : ℕ) : Finset (Fin n) := univ.filter fun i => k.testBit i = true

lemma mem_bitSet {n k : ℕ} (i : Fin n) : i ∈ bitSet n k ↔ k.testBit i = true := by
  simp [bitSet]

lemma bitSet_injective (n : ℕ) :
    Function.Injective fun k : Fin (2 ^ n) => bitSet n k := by
  intro a b h
  ext
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < n
  · have := Finset.ext_iff.mp h ⟨i, hi⟩
    simp only [mem_bitSet] at this
    exact Bool.eq_iff_iff.mpr this
  · have hp : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hi)
    rw [Nat.testBit_lt_two_pow (a.2.trans_le hp), Nat.testBit_lt_two_pow (b.2.trans_le hp)]

/-- Numbers below `2 ^ n` are the same as subsets of `Fin n`. -/
noncomputable def bitEquiv (n : ℕ) : Fin (2 ^ n) ≃ Finset (Fin n) :=
  Equiv.ofBijective (fun k => bitSet n k)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨bitSet_injective n, by simp⟩)

lemma mem_bitEquiv {n : ℕ} (k : Fin (2 ^ n)) (i : Fin n) :
    i ∈ bitEquiv n k ↔ (k : ℕ).testBit i = true := mem_bitSet i

/-- Numbers below `2 ^ 2 ^ n` are the same as families of subsets of `Fin n`. -/
noncomputable def familyEquiv (n : ℕ) : Fin (2 ^ 2 ^ n) ≃ Finset (Finset (Fin n)) :=
  (bitEquiv (2 ^ n)).trans (Equiv.finsetCongr (bitEquiv n))

/-- Containment of the bits of `i` in the bits of `j`. -/
def BitLE (i j : ℕ) : Prop := ∀ m, i.testBit m = true → j.testBit m = true

lemma BitLE.le {i j : ℕ} (h : BitLE i j) : i ≤ j := by
  have : i &&& j = i := by
    refine Nat.eq_of_testBit_eq fun m => ?_
    rw [Nat.testBit_and]
    have := h m
    cases hi : i.testBit m <;> simp_all
  rw [← this]
  exact Nat.and_le_right

lemma bitEquiv_subset_iff {n : ℕ} (i j : Fin (2 ^ n)) :
    bitEquiv n i ⊆ bitEquiv n j ↔ BitLE i j := by
  simp only [Finset.subset_iff, mem_bitEquiv, BitLE]
  refine ⟨fun h m hm => ?_, fun h m hm => h m hm⟩
  by_cases hmn : m < n
  · exact h (x := ⟨m, hmn⟩) hm
  · have hp : 2 ^ n ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hmn)
    rw [Nat.testBit_lt_two_pow (i.2.trans_le hp)] at hm
    simp at hm

/-- The innermost product of the formula tests containment of bits. -/
lemma prod_bits (i j : ℕ) :
    ∏ m ∈ Finset.range (i.log2 + 1),
      (1 - (i.testBit m).toNat + (i.testBit m).toNat * (j.testBit m).toNat) =
    open Classical in if BitLE i j then 1 else 0 := by
  classical
  split_ifs with h
  · refine Finset.prod_eq_one fun m _ => ?_
    have := h m
    cases hi : i.testBit m <;> simp_all
  · simp only [BitLE, not_forall] at h
    obtain ⟨m, hi, hj⟩ := h
    refine Finset.prod_eq_zero (i := m) ?_ (by simp_all)
    rw [Finset.mem_range, Nat.lt_succ_iff]
    by_contra hm
    have hlt : i < 2 ^ m := by
      refine (Nat.lt_log2_self (n := i)).trans_le ?_
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow hlt] at hi
    simp at hi

/-- The family coded by `k` has no containment `i ⊆ j` with `i < j`. -/
def Good (n k : ℕ) : Prop := ∀ j ∈ Finset.Icc 1 (2 ^ n), ∀ i ∈ Finset.range j,
  k.testBit i = true → k.testBit j = true → ¬ BitLE i j

lemma summand_eq (n k : ℕ) :
    ∏ j ∈ Finset.Icc 1 (2 ^ n), ∏ i ∈ Finset.range j,
      (1 - (k.testBit i).toNat * (k.testBit j).toNat * ∏ m ∈ Finset.range (i.log2 + 1),
        (1 - (i.testBit m).toNat + (i.testBit m).toNat * (j.testBit m).toNat)) =
    open Classical in if Good n k then 1 else 0 := by
  classical
  simp only [prod_bits]
  split_ifs with h
  · refine Finset.prod_eq_one fun j hj => Finset.prod_eq_one fun i hi => ?_
    have := h j hj i hi
    cases hki : k.testBit i <;> cases hkj : k.testBit j <;> simp_all
  · simp only [Good, not_forall, not_not] at h
    obtain ⟨j, hj, i, hi, hki, hkj, hb⟩ := h
    exact Finset.prod_eq_zero hj (Finset.prod_eq_zero hi (by simp [hki, hkj, hb]))

lemma isSperner_familyEquiv_iff {n : ℕ} (k : Fin (2 ^ 2 ^ n)) :
    IsSperner (familyEquiv n k) ↔ Good n k := by
  have hmem : ∀ i : Fin (2 ^ n), bitEquiv n i ∈ familyEquiv n k ↔ (k : ℕ).testBit i = true := by
    intro i
    simp [familyEquiv, ← mem_bitEquiv]
  constructor
  · intro h j hj i hi hki hkj hb
    have hij : i < j := Finset.mem_range.mp hi
    have hjn : j < 2 ^ n := by
      by_contra hjn
      have hp : 2 ^ 2 ^ n ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hjn)
      rw [Nat.testBit_lt_two_pow (k.2.trans_le hp)] at hkj
      simp at hkj
    let i' : Fin (2 ^ n) := ⟨i, hij.trans hjn⟩
    let j' : Fin (2 ^ n) := ⟨j, hjn⟩
    refine h ((hmem i').mpr hki) ((hmem j').mpr hkj) (fun he => ?_)
      ((bitEquiv_subset_iff i' j').mpr hb)
    have := congrArg Fin.val ((bitEquiv n).injective he)
    exact hij.ne this
  · intro h s hs t ht hne hst
    obtain ⟨i, rfl⟩ := (bitEquiv n).surjective s
    obtain ⟨j, rfl⟩ := (bitEquiv n).surjective t
    have hb := (bitEquiv_subset_iff i j).mp hst
    have hlt : (i : ℕ) < j := lt_of_le_of_ne hb.le fun he => hne (by rw [Fin.ext he])
    exact h j (Finset.mem_Icc.mpr ⟨by omega, j.2.le⟩) i (Finset.mem_range.mpr hlt)
      ((hmem i).mp hs) ((hmem j).mp ht) hb

/-- **Kisielewicz's formula.** The number of monotone Boolean functions of `n` variables is given by
Kisielewicz's sum. This is `DedekindNumber.M_eq_kisielewiczFormula` of Formal Conjectures. -/
theorem M_eq_kisielewiczFormula : M = kisielewiczFormula := by
  classical
  rw [M_eq_M']
  funext n
  simp only [M', kisielewiczFormula, summand_eq]
  rw [← Fin.sum_univ_eq_sum_range (fun k => if Good n k then 1 else 0), Finset.sum_boole,
    Nat.cast_id, ← Fintype.card_subtype]
  exact (Fintype.card_congr
    ((familyEquiv n).subtypeEquiv fun k => (isSperner_familyEquiv_iff k).symm)).symm

/-! ## The formula over the integers -/

lemma bit_eq (k i : ℕ) : bit k i = ((k.testBit i).toNat : ℤ) := by
  have h : k.testBit i = decide (k / 2 ^ i % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
  rw [bit, h, pow_succ, ← Nat.div_div_eq_div_mul]
  generalize k / 2 ^ i = q
  rcases Nat.mod_two_eq_zero_or_one q with h0 | h0
  · simp only [h0]
    simp
    omega
  · simp only [h0]
    simp
    omega

lemma prod_bit (i j : ℕ) :
    ∏ m ∈ Finset.range (i.log2 + 1), (1 - bit i m + bit i m * bit j m) =
      open Classical in if BitLE i j then (1 : ℤ) else 0 := by
  classical
  have h := congrArg (fun x : ℕ => (x : ℤ)) (prod_bits i j)
  simp only [Nat.cast_prod, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at h
  rw [← h]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [bit_eq, bit_eq]
  cases i.testBit m <;> cases j.testBit m <;> simp

/-- `Good` with the range of `j` usually printed. -/
def Good' (n k : ℕ) : Prop := ∀ j ∈ Finset.Icc 1 (2 ^ n - 1), ∀ i ∈ Finset.range j,
  k.testBit i = true → k.testBit j = true → ¬ BitLE i j

lemma summand_bit_eq (n k : ℕ) :
    ∏ j ∈ Finset.Icc 1 (2 ^ n - 1), ∏ i ∈ Finset.range j,
      (1 - bit k i * bit k j * ∏ m ∈ Finset.range (i.log2 + 1),
        (1 - bit i m + bit i m * bit j m)) =
    open Classical in if Good' n k then (1 : ℤ) else 0 := by
  classical
  simp only [prod_bit, bit_eq k]
  split_ifs with h
  · refine Finset.prod_eq_one fun j hj => Finset.prod_eq_one fun i hi => ?_
    have := h j hj i hi
    cases hki : k.testBit i <;> cases hkj : k.testBit j <;> simp_all
  · simp only [Good', not_forall, not_not] at h
    obtain ⟨j, hj, i, hi, hki, hkj, hb⟩ := h
    exact Finset.prod_eq_zero hj (Finset.prod_eq_zero hi (by simp [hki, hkj, hb]))

lemma good'_iff {n k : ℕ} (hk : k < 2 ^ 2 ^ n) : Good' n k ↔ Good n k := by
  have hp : 0 < 2 ^ n := by positivity
  refine ⟨fun h j hj i hi hki hkj => ?_, fun h j hj => h j ?_⟩
  · rw [Finset.mem_Icc] at hj
    rcases Nat.lt_or_ge j (2 ^ n) with hjn | hjn
    · exact h j (Finset.mem_Icc.mpr ⟨hj.1, by omega⟩) i hi hki hkj
    · have hp : 2 ^ 2 ^ n ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hjn
      rw [Nat.testBit_lt_two_pow (hk.trans_le hp)] at hkj
      simp at hkj
  · rw [Finset.mem_Icc] at hj ⊢
    omega

lemma good'_zero (n : ℕ) : Good' n 0 := by
  intro j _ i _ h
  simp at h

lemma good'_top (n : ℕ) : Good' n (2 ^ 2 ^ n) := by
  intro j hj i hi h
  rw [Finset.mem_Icc] at hj
  rw [Finset.mem_range] at hi
  rw [Nat.testBit_two_pow_of_ne (by omega)] at h
  simp at h

/-- **Kisielewicz's formula**, with integer arithmetic, floor-function digits and the ranges usually
printed: `k` from `1` to `2 ^ 2 ^ n`, `j` from `1` to `2 ^ n - 1` and `i` from `0` to `j - 1`. The
upper limit `log₂ i` of the last product is `0` when `i = 0`. -/
theorem M_eq_sum_bit (n : ℕ) :
    (M n : ℤ) = ∑ k ∈ Icc 1 (2 ^ 2 ^ n), ∏ j ∈ Icc 1 (2 ^ n - 1), ∏ i ∈ range j,
      (1 - bit k i * bit k j * ∏ m ∈ range (i.log2 + 1), (1 - bit i m + bit i m * bit j m)) := by
  classical
  simp only [summand_bit_eq]
  set g : ℕ → ℤ := fun k => if Good' n k then 1 else 0 with hg
  have hI : Finset.Icc 1 (2 ^ 2 ^ n) = Finset.Ico 1 (2 ^ 2 ^ n + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have h0 : g 0 = 1 := by simp [hg, good'_zero n]
  have h1 : g (2 ^ 2 ^ n) = 1 := by simp [hg, good'_top n]
  have hs : ∑ k ∈ Finset.Icc 1 (2 ^ 2 ^ n), g k = ∑ k ∈ Finset.range (2 ^ 2 ^ n), g k := by
    have ha := Finset.sum_range_succ g (2 ^ 2 ^ n)
    have hb := Finset.sum_range_succ' g (2 ^ 2 ^ n)
    have hc : ∑ k ∈ Finset.Icc 1 (2 ^ 2 ^ n), g k =
        ∑ k ∈ Finset.range (2 ^ 2 ^ n), g (k + 1) := by
      rw [hI, Finset.sum_Ico_eq_sum_range]
      simp [add_comm]
    linarith
  rw [hs, M_eq_kisielewiczFormula, kisielewiczFormula]
  simp only [summand_eq]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [hg, good'_iff (Finset.mem_range.mp hk)]

end DedekindNumber

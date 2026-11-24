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
# Dedekind numbers, and their two descriptions

Everything here except `bit` is copied from `FormalConjectures/Wikipedia/DedekindNumber.lean` of
google-deepmind/formal-conjectures (Apache License 2.0), including the proof of `M_eq_M'`, which is
theirs. Their `category` attributes are removed.
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

/-- A Sperner family (antichain) of subsets of `Fin n`: a family of sets such that
    no member is a subset of another. -/
def IsSperner {n : ℕ} (A : Finset (Finset (Fin n))) : Prop :=
  IsAntichain (fun s t => s ⊆ t) (A : Set (Finset (Fin n)))

instance isSpernerDecidable {n : ℕ} :
    DecidablePred (fun A : Finset (Finset (Fin n)) => IsSperner A) :=
  fun A => by
    unfold IsSperner IsAntichain Set.Pairwise
    simp only [Finset.mem_coe, Pi.compl_apply, compl_iff_not]
    exact inferInstance

/-- $M'(n)$ is the number of antichains (Sperner families) of subsets of `Fin n`. -/
def M' (n : ℕ) : ℕ :=
  Fintype.card {A : Finset (Finset (Fin n)) // IsSperner A}

/-! ## Equivalence of M and M' -/

/-- The indicator function of a finset: `χ s i = true ↔ i ∈ s`. -/
def χ {n : ℕ} (s : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ s)

/-- The support of a Boolean-valued function: `supp v = {i | v i = true}`. -/
def supp {n : ℕ} (v : Fin n → Bool) : Finset (Fin n) :=
  univ.filter (fun i => v i = true)

/-- Forward map: monotone function → Sperner family (the minimal true sets). -/
def toSperner {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Finset (Fin n)) :=
  univ.filter (fun s =>
    f (χ s) = true ∧ ∀ t : Finset (Fin n), t ⊆ s → f (χ t) = true → s ⊆ t)

/-- Backward map: Sperner family → monotone Boolean function. -/
def fromSperner {n : ℕ} (A : Finset (Finset (Fin n))) (v : Fin n → Bool) : Bool :=
  decide (∃ s ∈ A, ∀ i ∈ s, v i = true)

/-! ### Helper lemmas about χ and supp -/

lemma χ_supp {n : ℕ} (v : Fin n → Bool) : χ (supp v) = v := by
  funext i; simp [χ, supp]

lemma supp_χ {n : ℕ} (s : Finset (Fin n)) : supp (χ s) = s := by
  ext i
  simp [χ, supp]

lemma χ_le_iff {n : ℕ} (s t : Finset (Fin n)) : χ s ≤ χ t ↔ s ⊆ t := by
  simp [χ, Pi.le_def, Finset.subset_iff, Bool.le_iff_imp]

lemma mem_supp_iff {n : ℕ} (v : Fin n → Bool) (i : Fin n) : i ∈ supp v ↔ v i = true := by
  simp [supp]

lemma toSperner_isSperner {n : ℕ} (f : (Fin n → Bool) → Bool) (_ : Monotone f) :
    IsSperner (toSperner f) := by
  intro s hs t ht hst; simp_all +decide [ Finset.ext_iff]
  contrapose! hst; unfold toSperner at *; aesop

lemma fromSperner_monotone {n : ℕ} (A : Finset (Finset (Fin n))) (_ : IsSperner A) :
    Monotone (fromSperner A) := by
      intro v w hvw hfv
      obtain ⟨s, hsA, hs⟩ : ∃ s ∈ A, s ⊆ supp v := by
        unfold fromSperner at hfv
        simp_all +decide [ Finset.subset_iff, mem_supp_iff ]
      have hs_w : s ⊆ supp w := by
        intro i hi; have := hs hi
        simp_all +decide [ Finset.subset_iff, mem_supp_iff ]
        exact Bool.eq_false_imp_eq_true.mp fun a ↦ hvw i (hs hi)
      exact decide_eq_true
        ( ⟨ s, hsA, fun i hi => by simpa using Finset.mem_filter.mp ( hs_w hi ) |>.2 ⟩ )

/-- Every true set of a monotone Boolean function contains a minimal true set. -/
lemma exists_minimal_true_subset {n : ℕ} {f : (Fin n → Bool) → Bool} (_ : Monotone f)
    {s : Finset (Fin n)} (hs : f (χ s) = true) :
    ∃ t, t ⊆ s ∧ f (χ t) = true ∧ ∀ u, u ⊆ t → f (χ u) = true → t ⊆ u := by
      obtain ⟨t, ht₁, ht₂⟩ :
        ∃ t ∈ {t : Finset (Fin n) | t ⊆ s ∧ f (χ t) = true},
        ∀ u ∈ {t : Finset (Fin n) | t ⊆ s ∧ f (χ t) = true}, t.card ≤ u.card := by
        apply_rules [ Set.exists_min_image ]
        · exact Set.finite_iff_bddAbove.mpr ⟨ s, fun t ht => ht.1 ⟩
        · exact ⟨ s, Finset.Subset.refl _, hs ⟩
      refine' ⟨ t, ht₁.1, ht₁.2, fun u hu hu' => _ ⟩
      exact Classical.not_not.1 fun h =>
        not_lt_of_ge ( ht₂ u ⟨ hu.trans ht₁.1, hu' ⟩ )
        ( Finset.card_lt_card <| Finset.ssubset_iff_subset_ne.2 ⟨ hu, by aesop ⟩ )

/-- Converting a monotone function to a Sperner family and back yields the same function. -/
lemma fromSperner_toSperner {n : ℕ} (f : (Fin n → Bool) → Bool) (hf : Monotone f) :
    fromSperner (toSperner f) = f := by
  funext v
  by_cases h : f v <;> simp_all +decide [ fromSperner ]
  · obtain ⟨t, ht₁, ht₂⟩ : ∃ t : Finset (Fin n),
    t ⊆ Finset.univ.filter (fun i => v i = true) ∧
    f (χ t) = true ∧
    ∀ u : Finset (Fin n), u ⊆ t → f (χ u) = true → t ⊆ u := by
      apply exists_minimal_true_subset hf;
      convert h using 2
      exact funext fun i => by unfold χ; aesop;
    exact ⟨ t, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, ht₂.1, ht₂.2 ⟩,
    fun i hi => Finset.mem_filter.mp ( ht₁ hi ) |>.2 ⟩
  · intro s hs; contrapose! h; simp_all +decide [ toSperner ]
    refine' hf _ hs.1
    intro i; by_cases hi : i ∈ s <;> simp_all +decide [ χ ]

/-- Converting a Sperner family to a monotone function and back yields the same family. -/
lemma toSperner_fromSperner {n : ℕ} (A : Finset (Finset (Fin n))) (hA : IsSperner A) :
    toSperner (fromSperner A) = A := by
  ext s; simp [toSperner, fromSperner]
  constructor <;> intro hs
  all_goals generalize_proofs at *
  · obtain ⟨ ⟨ t, ht₁, ht₂ ⟩, ht₃ ⟩ := hs
    convert ht₁ using 1
    exact subset_antisymm ( ht₃ t ( by unfold χ at ht₂; aesop ) t ht₁ ( by unfold χ; aesop ) )
      ( by unfold χ at ht₂; aesop )
  · refine' ⟨ ⟨ s, hs, _ ⟩, _ ⟩ <;> simp_all +decide [ IsSperner ]
    · exact fun i hi => by unfold χ; aesop
    · intro t ht x hx hx'; have := hA hx hs; simp_all +decide [ Finset.subset_iff, χ ]
/--
  The set of monotone Boolean functions on `n` variables is in bijection
  with the set of Sperner families of subsets of `Fin n`.
-/
def equivMonotoneSperner (n : ℕ) :
    {f : (Fin n → Bool) → Bool // Monotone f} ≃
    {A : Finset (Finset (Fin n)) // IsSperner A} where
  toFun := fun ⟨f, hf⟩ => ⟨toSperner f, toSperner_isSperner f hf⟩
  invFun := fun ⟨A, hA⟩ => ⟨fromSperner A, fromSperner_monotone A hA⟩
  left_inv := fun ⟨f, hf⟩ => Subtype.ext (fromSperner_toSperner f hf)
  right_inv := fun ⟨A, hA⟩ => Subtype.ext (toSperner_fromSperner A hA)

theorem M_eq_M' : M  = M' := by
  ext n
  exact Fintype.card_congr (equivMonotoneSperner n)

/-- Kisielewicz's sum, as a natural number, exactly as Formal Conjectures writes it. The number `k` runs
over `0, …, 2 ^ 2 ^ n - 1`, and `i.testBit m` is the `m`-th binary digit of `i`. Every subtraction takes
a number that is `0` or `1` away from `1`, so truncation plays no role. -/
def kisielewiczFormula (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 ^ (2 ^ n)), ∏ j ∈ Finset.Icc 1 (2 ^ n), ∏ i ∈ Finset.range j,
    (1 - (k.testBit i).toNat * (k.testBit j).toNat * ∏ m ∈ Finset.range (i.log2 + 1),
      (1 - (i.testBit m).toNat + (i.testBit m).toNat * (j.testBit m).toNat))

/-- The `i`-th binary digit of `k`, as the integer `⌊k / 2 ^ i⌋ - 2 ⌊k / 2 ^ (i + 1)⌋`. -/
def bit (k i : ℕ) : ℤ := (k / 2 ^ i : ℕ) - 2 * (k / 2 ^ (i + 1) : ℕ)

end DedekindNumber

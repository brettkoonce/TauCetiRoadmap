import Mathlib
import TauCeti.Computability.Simple.Basic

/-!
# Plain and prefix-free Kolmogorov complexity: target signatures

The roadmap is `README.md`; this file is not the roadmap. It states the roadmap's headline
results against the pinned Mathlib and Tau Ceti, with the few definitions they need, every
theorem with `sorry` and every definition with a real body.

Strings are `List Bool`. A description map is a partial function `List Bool →. List Bool`; the
complexity of `x` relative to it is the least length of a description of `x`, in `ℕ∞`, and `⊤`
when `x` has none.
-/

open scoped ENNReal

namespace TauCetiRoadmap.KolmogorovComplexity

/-- 1.1 The complexity of `x` relative to a description map `D`: the least length of a string
`p` with `D p = x`, and `⊤` when `x` has no description. -/
noncomputable def descComplexity (D : List Bool →. List Bool) (x : List Bool) : ℕ∞ :=
  ⨅ (p : List Bool) (_ : x ∈ D p), (p.length : ℕ∞)

/-- 1.1 An optimal description map: partial computable and, up to an additive constant, at
least as good as every partial computable description map. -/
structure IsOptimalDescriptionMap (D : List Bool →. List Bool) : Prop where
  /-- An optimal description map is partial computable. -/
  partrec : Partrec D
  /-- An optimal description map is not worse than any partial computable one. -/
  le_add : ∀ D' : List Bool →. List Bool, Partrec D' →
    ∃ c : ℕ, ∀ x, descComplexity D x ≤ descComplexity D' x + c

/-- 1.2 The invariance theorem (Solomonoff–Kolmogorov): an optimal description map exists. -/
theorem exists_isOptimalDescriptionMap : ∃ D, IsOptimalDescriptionMap D := by
  sorry

/-- 1.3 Complexity is at most length plus a constant, and a partial computable map raises
complexity by at most a constant. -/
theorem IsOptimalDescriptionMap.upper_bounds {D : List Bool →. List Bool}
    (hD : IsOptimalDescriptionMap D) :
    (∃ c : ℕ, ∀ x, descComplexity D x ≤ x.length + c) ∧
      ∀ A : List Bool →. List Bool, Partrec A →
        ∃ c : ℕ, ∀ x y, y ∈ A x → descComplexity D y ≤ descComplexity D x + c := by
  sorry

/-- 2.1 Counting, for every description map: fewer than `2 ^ k` strings have complexity below
`k`, so fewer than `2 ^ k` elements of a finite set `A` do; and at every length `n` some string
has complexity at least `n`. -/
theorem descComplexity_counting (D : List Bool →. List Bool) :
    (∀ k : ℕ, {x | descComplexity D x < k}.encard < (2 : ℕ∞) ^ k) ∧
      (∀ (A : Finset (List Bool)) (k : ℕ),
        A.card + 1 ≤ (A.filter fun x => (k : ℕ∞) ≤ descComplexity D x).card + 2 ^ k) ∧
      ∀ n : ℕ, ∃ x : List Bool, x.length = n ∧ (n : ℕ∞) ≤ descComplexity D x := by
  sorry

/-- 2.2 Enumerable families of small sets consist of simple strings: if `V` is c.e. and its
`n`-th section has fewer than `2 ^ n` elements, its members have complexity below `n + c`. -/
theorem IsOptimalDescriptionMap.exists_lt_add_of_rePred {D : List Bool →. List Bool}
    (hD : IsOptimalDescriptionMap D) {V : Set (ℕ × List Bool)} (hV : REPred (· ∈ V))
    (hcard : ∀ n, {x | (n, x) ∈ V}.encard < (2 : ℕ∞) ^ n) :
    ∃ c : ℕ, ∀ n x, (n, x) ∈ V → descComplexity D x < n + c := by
  sorry

/-- 3.1 Complexity relative to a partial computable map is upper semicomputable: the family of
sets `{x | C_D(x) < n}`, as a set of pairs `(n, x)`, is c.e. -/
theorem rePred_descComplexity_lt {D : List Bool →. List Bool} (hD : Partrec D) :
    REPred fun q : ℕ × List Bool => descComplexity D q.2 < q.1 := by
  sorry

/-- 3.2 Berry's paradox: a partial computable lower bound of the complexity is bounded, and the
complexity is not computable. -/
theorem IsOptimalDescriptionMap.lowerBound_bounded {D : List Bool →. List Bool}
    (hD : IsOptimalDescriptionMap D) :
    (∀ k : List Bool →. ℕ, Partrec k → (∀ x n, n ∈ k x → (n : ℕ∞) ≤ descComplexity D x) →
        ∃ B : ℕ, ∀ x n, n ∈ k x → n ≤ B) ∧
      ¬∃ f : List Bool → ℕ, Computable f ∧ ∀ x, (f x : ℕ∞) = descComplexity D x := by
  sorry

/-- 3.3 The strings of complexity less than half their length form a simple set in Post's
sense. -/
theorem IsOptimalDescriptionMap.simple_compressible {D : List Bool →. List Bool}
    (hD : IsOptimalDescriptionMap D) :
    Set.Simple {x : List Bool | 2 * descComplexity D x < x.length} := by
  sorry

/-- 4.1 A prefix-free description map: partial computable, with a prefix-free domain. -/
structure IsPrefixFreeDescriptionMap (D : List Bool →. List Bool) : Prop where
  /-- A prefix-free description map is partial computable. -/
  partrec : Partrec D
  /-- No string of the domain is a proper prefix of another. -/
  prefixFree : InformationTheory.IsPrefixFree {p | (D p).Dom}

/-- 4.1 An optimal prefix-free description map: a prefix-free description map that is, up to an
additive constant, at least as good as every prefix-free description map. -/
structure IsOptimalPrefixFreeDescriptionMap (D : List Bool →. List Bool) : Prop
    extends IsPrefixFreeDescriptionMap D where
  /-- It is not worse than any prefix-free description map. -/
  le_add : ∀ D' : List Bool →. List Bool, IsPrefixFreeDescriptionMap D' →
    ∃ c : ℕ, ∀ x, descComplexity D x ≤ descComplexity D' x + c

/-- 4.1 An optimal prefix-free description map exists. -/
theorem exists_isOptimalPrefixFreeDescriptionMap : ∃ D, IsOptimalPrefixFreeDescriptionMap D := by
  sorry

/-- 4.2 Kraft's inequality for complexity: if `D` has a prefix-free domain, the sum of
`2 ^ (-C_D(x))` over the strings with a description is at most `1`. -/
theorem tsum_two_inv_pow_descComplexity_le_one {D : List Bool →. List Bool}
    (hD : InformationTheory.IsPrefixFree {p | (D p).Dom}) :
    ∑' x : {x : List Bool // descComplexity D x ≠ ⊤},
      (2⁻¹ : ℝ≥0∞) ^ (descComplexity D x).toNat ≤ 1 := by
  sorry

/-- 4.3 If `D` has a prefix-free domain, its complexity is not bounded by length plus a
constant. -/
theorem not_exists_descComplexity_le_length_add {D : List Bool →. List Bool}
    (hD : InformationTheory.IsPrefixFree {p | (D p).Dom}) :
    ¬∃ c : ℕ, ∀ x, descComplexity D x ≤ x.length + c := by
  sorry

/-- 4.4 Plain and prefix-free complexity: `C(x) ≤ K(x) + c` and
`K(x) ≤ C(x) + 2 log₂ C(x) + c`. -/
theorem IsOptimalPrefixFreeDescriptionMap.compare_plain {U D : List Bool →. List Bool}
    (hU : IsOptimalDescriptionMap U) (hD : IsOptimalPrefixFreeDescriptionMap D) :
    (∃ c : ℕ, ∀ x, descComplexity U x ≤ descComplexity D x + c) ∧
      ∃ c : ℕ, ∀ (x : List Bool) (m : ℕ), descComplexity U x ≤ m →
        descComplexity D x ≤ (m + 2 * Nat.log 2 m + c : ℕ) := by
  sorry

end TauCetiRoadmap.KolmogorovComplexity

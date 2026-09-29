/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveOverlapModuleLocalization

/-!
# Common denominators on projective charts

Actual overlap sections have chart numerators after multiplying by a power of
the coordinate ratio. A finite family has one common exponent, even when its
members lie on different overlaps. Equalities on those overlaps are likewise
annihilated by one exponent. All maps are the actual restrictions constructed
in `ProjectiveOverlapModuleLocalization`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

universe u v

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)
variable (F : (space R ι).Modules) [F.IsFinitePresentation]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every actual overlap section has a numerator on the first chart. -/
lemma chartOverlap_exists_numerator (i j : ι) (s : overlapSections R ι F i j) :
    ∃ (n : ℕ) (t : chartSections R ι F i),
      chartOverlapRestriction R ι F i j t = coordinate R ι i j ^ n • s := by
  obtain ⟨n, t, ht⟩ := IsLocalizedModule.Away.surj
    (chartOverlapRestriction R ι F i j) (coordinate R ι i j) s
  exact ⟨n, t, ht.symm⟩

/-- Equality after actual restriction is exactly equality after a coordinate power. -/
lemma chartOverlap_eq_iff (i j : ι) (s t : chartSections R ι F i) :
    chartOverlapRestriction R ι F i j s = chartOverlapRestriction R ι F i j t ↔
      ∃ n : ℕ, coordinate R ι i j ^ n • s = coordinate R ι i j ^ n • t := by
  constructor
  · exact IsLocalizedModule.Away.exists_of_eq (coordinate R ι i j)
  · rintro ⟨n, hn⟩
    exact (IsLocalizedModule.eq_iff_exists (.powers (coordinate R ι i j))
      (chartOverlapRestriction R ι F i j)).mpr ⟨⟨_, n, rfl⟩, hn⟩

/-- The kernel of overlap restriction consists of sections killed by a coordinate power. -/
lemma chartOverlap_zero_iff (i j : ι) (s : chartSections R ι F i) :
    chartOverlapRestriction R ι F i j s = 0 ↔
      ∃ n : ℕ, coordinate R ι i j ^ n • s = 0 := by
  simpa only [map_zero, smul_zero] using chartOverlap_eq_iff R ι F i j s 0

private lemma coordinate_power_eq_of_le {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (r : A) {s t : M} {n N : ℕ} (h : r ^ n • s = r ^ n • t)
    (hn : n ≤ N) : r ^ N • s = r ^ N • t := by
  simpa only [smul_smul, ← pow_add, Nat.sub_add_cancel hn] using
    congrArg (fun x : M ↦ r ^ (N - n) • x) h

omit [F.IsFinitePresentation] in
/-- An existing numerator can be raised to any larger denominator exponent. -/
lemma chartOverlap_raise_numerator (i j : ι) (s : overlapSections R ι F i j)
    (t : chartSections R ι F i) {n N : ℕ}
    (ht : chartOverlapRestriction R ι F i j t = coordinate R ι i j ^ n • s)
    (hn : n ≤ N) :
    chartOverlapRestriction R ι F i j (coordinate R ι i j ^ (N - n) • t) =
      coordinate R ι i j ^ N • s := by
  rw [map_smul, ht, smul_smul, ← pow_add, Nat.sub_add_cancel hn]

variable {κ : Type v} [Finite κ]

/-- One exponent clears a finite dependent family on possibly different overlaps. -/
theorem overlapFamily_clearDenominators (i j : κ → ι)
    (s : ∀ k, overlapSections R ι F (i k) (j k)) :
    ∃ (N : ℕ) (t : ∀ k, chartSections R ι F (i k)),
      ∀ k, chartOverlapRestriction R ι F (i k) (j k) (t k) =
        coordinate R ι (i k) (j k) ^ N • s k := by
  classical
  let := Fintype.ofFinite κ
  choose n t ht using fun k ↦ chartOverlap_exists_numerator R ι F (i k) (j k) (s k)
  let N := Finset.univ.sup n
  refine ⟨N, fun k ↦ coordinate R ι (i k) (j k) ^ (N - n k) • t k, fun k ↦ ?_⟩
  exact chartOverlap_raise_numerator R ι F (i k) (j k) (s k) (t k) (ht k)
    (Finset.le_sup (Finset.mem_univ k))

/-- A finite family on one overlap has a common coordinate denominator. -/
theorem overlapSections_clearDenominators (i j : ι)
    (s : κ → overlapSections R ι F i j) :
    ∃ (N : ℕ) (t : κ → chartSections R ι F i),
      ∀ k, chartOverlapRestriction R ι F i j (t k) =
        coordinate R ι i j ^ N • s k :=
  overlapFamily_clearDenominators R ι F (fun _ ↦ i) (fun _ ↦ j) s

/-- The same common-denominator statement with the overlap-ring powers action explicit. -/
theorem overlapFamily_clearDenominators_toOverlap (i j : κ → ι)
    (s : ∀ k, overlapSections R ι F (i k) (j k)) :
    ∃ (N : ℕ) (t : ∀ k, chartSections R ι F (i k)),
      ∀ k, chartOverlapRestriction R ι F (i k) (j k) (t k) =
        toOverlap R ι (i k) (j k) (coordinate R ι (i k) (j k)) ^ N • s k := by
  simpa only [overlapSections_pow_smul] using overlapFamily_clearDenominators R ι F i j s

/-- One coordinate power annihilates all equalities on a finite family of overlaps. -/
theorem overlapFamily_annihilateEqualities (i j : κ → ι)
    (s t : ∀ k, chartSections R ι F (i k))
    (h : ∀ k, chartOverlapRestriction R ι F (i k) (j k) (s k) =
      chartOverlapRestriction R ι F (i k) (j k) (t k)) :
    ∃ N : ℕ, ∀ k,
      coordinate R ι (i k) (j k) ^ N • s k = coordinate R ι (i k) (j k) ^ N • t k := by
  classical
  let := Fintype.ofFinite κ
  choose n hn using fun k ↦ (chartOverlap_eq_iff R ι F (i k) (j k) (s k) (t k)).mp (h k)
  refine ⟨Finset.univ.sup n, fun k ↦ ?_⟩
  exact coordinate_power_eq_of_le _ (hn k) (Finset.le_sup (Finset.mem_univ k))

/-- Common powers detect all overlap equalities, in both directions. -/
theorem overlapFamily_equalities_iff (i j : κ → ι)
    (s t : ∀ k, chartSections R ι F (i k)) :
    (∀ k, chartOverlapRestriction R ι F (i k) (j k) (s k) =
      chartOverlapRestriction R ι F (i k) (j k) (t k)) ↔
      ∃ N : ℕ, ∀ k,
        coordinate R ι (i k) (j k) ^ N • s k = coordinate R ι (i k) (j k) ^ N • t k := by
  refine ⟨overlapFamily_annihilateEqualities R ι F i j s t, ?_⟩
  rintro ⟨N, hN⟩ k
  exact (chartOverlap_eq_iff R ι F (i k) (j k) (s k) (t k)).mpr ⟨N, hN k⟩

/-- Finite families of equalities on a fixed overlap have one annihilating exponent. -/
theorem chartSections_overlapEqualities (i j : ι) (s t : κ → chartSections R ι F i)
    (h : ∀ k, chartOverlapRestriction R ι F i j (s k) =
      chartOverlapRestriction R ι F i j (t k)) :
    ∃ N : ℕ, ∀ k, coordinate R ι i j ^ N • s k = coordinate R ι i j ^ N • t k :=
  overlapFamily_annihilateEqualities R ι F (fun _ ↦ i) (fun _ ↦ j) s t h

/-- A finite family in the kernels of actual overlap restrictions is killed uniformly. -/
theorem overlapFamily_annihilateKernels (i j : κ → ι)
    (s : ∀ k, chartSections R ι F (i k))
    (h : ∀ k, chartOverlapRestriction R ι F (i k) (j k) (s k) = 0) :
    ∃ N : ℕ, ∀ k, coordinate R ι (i k) (j k) ^ N • s k = 0 := by
  simpa only [smul_zero] using
    overlapFamily_annihilateEqualities R ι F i j s (fun _ ↦ 0)
      (fun k ↦ by simpa only [map_zero] using h k)

/-- All sufficiently large exponents clear the same finite family of denominators. -/
theorem overlapFamily_eventually_clearDenominators (i j : κ → ι)
    (s : ∀ k, overlapSections R ι F (i k) (j k)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : ∀ k, chartSections R ι F (i k),
      ∀ k, chartOverlapRestriction R ι F (i k) (j k) (t k) =
        coordinate R ι (i k) (j k) ^ n • s k := by
  obtain ⟨N, t, ht⟩ := overlapFamily_clearDenominators R ι F i j s
  refine ⟨N, fun n hn ↦ ⟨fun k ↦ coordinate R ι (i k) (j k) ^ (n - N) • t k,
    fun k ↦ ?_⟩⟩
  exact chartOverlap_raise_numerator R ι F (i k) (j k) (s k) (t k) (ht k) hn

/-- All sufficiently large exponents annihilate the finite family of equalities. -/
theorem overlapFamily_eventually_annihilateEqualities (i j : κ → ι)
    (s t : ∀ k, chartSections R ι F (i k))
    (h : ∀ k, chartOverlapRestriction R ι F (i k) (j k) (s k) =
      chartOverlapRestriction R ι F (i k) (j k) (t k)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ k,
      coordinate R ι (i k) (j k) ^ n • s k = coordinate R ι (i k) (j k) ^ n • t k := by
  obtain ⟨N, hN⟩ := overlapFamily_annihilateEqualities R ι F i j s t h
  exact ⟨N, fun _ hn k ↦ coordinate_power_eq_of_le _ (hN k) hn⟩

end FLT.Mazur.ProjectiveSpace

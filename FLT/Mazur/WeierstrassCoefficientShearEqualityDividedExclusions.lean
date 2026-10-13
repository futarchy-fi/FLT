/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearEqualityOpenExclusions
public import FLT.Mazur.WeierstrassDividedPrecedingAtlasRange
public import FLT.Mazur.WeierstrassCoefficientShearAtlasComparison

/-!
# Full divided-chart exclusions in the arbitrary-root equality atlas

The entire divided equation factors through the completed projective component.
Every earlier chart lies in the full preceding exterior, so all these original
atlas intersections are empty, including the initial equation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (hs : algebraMap R S (π ^ (start + j)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (hc : IsUnit (algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6))
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S (Data.b6 d)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "hsNext" => show algebraMap R S (π ^ (start + (j + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
local notation "conic" => coefficientShearRetainedConic hπ data S r (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j)) hs hp h3 h4 hr
local notation "G" => coefficientShearGluedIso hπ data S r (j + 1) hj
local notation "C" => coefficientShearRootEqualityComponent
  hπ data S r j hj hs hp h3 h4 hc hr a ha
local notation "q" => coefficientShearEqualityConicParameter
  data S r j hj hs hp h3 h4 hc hr a ha
local notation "tensorConic" => tensorShearConicImmersion W (π ^ (start + j)) π
  (d).b3 (d).b4 (d).b6 S r hs hp h3 h4 hr
local notation "old" => olderGlobalTensorChart hπ data S j hj 0 hj

local notation "A" => coefficientShearAtlasMap hπ data S r (j + 1) hj
local notation "v" => coefficientShearEqualityDividedParameter
  data S r j hj hp h3 h4 hc hr a ha

/-- Every original divided-chart point comes from the complete equality component. -/
theorem coefficientShearEqualityDivided_range_subset_component :
    Set.range (A (.inl 1)) ⊆ Set.range (C ≫ (G).hom) := by
  rintro _ ⟨z, rfl⟩
  refine ⟨v z, ?_⟩
  have H := congrArg (· ≫ (G).hom)
    (coefficientShearEqualityDividedParameter_component
      hπ data S r j hj hs hp h3 h4 hc hr a ha)
  rw [coefficientShearGluedIso_chart] at H
  exact congrArg (fun f => f z) H

include hs hp h3 h4 hc hr a ha

/-- Every whole original indexed chart beyond the final neighbor misses the divided chart. -/
theorem coefficientShearEqualityDivided_nonadjacent_disjoint
    (k : Fin (j + 1 + 3)) (hk : 3 ≤ k.val) :
    Disjoint (Set.range (A (.inl 1)))
      (Set.range (globalTensorAtlasMap hπ data S (j + 1) hj k)) := by
  let i : Fin (j + 1) := ⟨k.val - 3, by omega⟩
  have H := precedingGlobalTensorAtlas_range_subset hπ data j hj 0 hj S i
  have hi : (Fin.succ ⟨i.val + 1 + 0 + 1, by omega⟩ : Fin (j + 1 + 0 + 3)) =
      k := Fin.ext (by dsimp [i]; omega)
  rw [hi] at H
  exact ((coefficientShearEqualityComponent_precedingExterior_disjoint
    hπ data S r j hj hs hp h3 h4 hc hr a ha).mono_left
    (coefficientShearEqualityDivided_range_subset_component
      hπ data S r j hj hs hp h3 h4 hc hr a ha)).mono_right H

/-- The full divided equation misses every earlier retained equation. -/
theorem coefficientShearEqualityDivided_retained_disjoint (i : Fin (j + 1))
    (hi : i.val < j) :
    Disjoint (Set.range (A (.inl 1))) (Set.range (A (.inr i))) := by
  rw [coefficientShearAtlasMap_range hπ data S r (j + 1) hj (.inr i)]
  apply coefficientShearEqualityDivided_nonadjacent_disjoint
    hπ data S r j hj hs hp h3 h4 hc hr a ha
  change 3 ≤ j + 1 - i.val + 1
  omega

/-- The entire initial equation misses the full divided equation, including at first depth. -/
theorem coefficientShearEqualityDivided_initial_disjoint :
    Disjoint (Set.range (A (.inl 1))) (Set.range (A (.inl 2))) := by
  rw [coefficientShearAtlasMap_range hπ data S r (j + 1) hj (.inl 2)]
  apply coefficientShearEqualityDivided_nonadjacent_disjoint
    hπ data S r j hj hs hp h3 h4 hc hr a ha
  change 3 ≤ j + 1 + 2
  omega

/-- The full divided equation misses infinity at positive scale. -/
theorem coefficientShearEqualityDivided_infinity_disjoint (hpos : 0 < start + j) :
    Disjoint (Set.range (A (.inl 1))) (Set.range (A (.inl 0))) :=
  (coefficientShearEqualityComponent_infinity_disjoint
    hπ data S r j hj hs hp h3 h4 hc hr a ha hpos).mono_left
    (coefficientShearEqualityDivided_range_subset_component
      hπ data S r j hj hs hp h3 h4 hc hr a ha)

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothOriginalSubgroupCoefficient
public import FLT.Mazur.CompatibleSubgroupIsoSectionSquare

/-!
# Original generators around the smooth coefficient square

Both coefficient paths retain the actual Cartier generator section and every
power, through the full compatible comparisons of the actual subgroups.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  compatibleBaseChangeCompEq completeSmoothOriginalSubgroupIso completeFieldCoefficientSubgroupIso
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
  (M : Type) [Field M] [Algebra L M]
  {Z : Scheme} (r : Z ⟶ exactVeroneseProj K n h) (s : Z ⟶ Spec (.of M))
  (ht : IsPullback r s (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom ((algebraMap L M).comp a))))
local notation "aM" => RingHom.comp (algebraMap L M) a
local notation "haM" => Iff.mpr (map_ne_zero (algebraMap L M)) ha
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap L M))
local notation "u" => Spec.map (CommRingCat.ofHom a)
local notation "v" => Spec.map (CommRingCat.ofHom aM)
local notation "H" => completeOriginalFiniteSubgroup K n h
local notation "cL" => completeSmoothOriginalSubgroupIso K n h L a ha p q hs
local notation "cM" => completeSmoothOriginalSubgroupIso K n h M aM haM r s ht
local notation "cLM" => completeFieldCoefficientSubgroupIso K n h L a ha p q hs M r s ht
local notation "cD" => compatibleBaseChangeCompEq (H) u b v
  (Eq.symm (completeCoefficientSpec_comp K L a M))

local notation "P" => completeOriginalGenerator K n h
local notation "QM" => completeFieldGenerator K n h M aM haM r s ht
local notation "cPath" => CompatibleIso.trans
  (CompatibleIso.trans (cD) (CompatibleIso.baseChange (cL) b)) (cLM)

/-- The iterated coefficient path retains the original complete Cartier generator. -/
theorem completeSmoothOriginalSubgroupIso_coefficient_generator :
    pullSection v (P) ≫ (cPath).subgroup.hom = QM := by
  rw [completeSmoothOriginalSubgroupIso_coefficient]
  exact completeSmoothOriginalSubgroupIso_generator K n h M aM haM r s ht

/-- The direct and iterated paths retain every actual generator power. -/
theorem completeSmoothOriginalSubgroupIso_coefficient_generator_pow (m : ℕ) :
    pullSection v ((P) ^ m) ≫ (cPath).subgroup.hom = (QM) ^ m := by
  rw [completeSmoothOriginalSubgroupIso_coefficient]
  exact completeSmoothOriginalSubgroupIso_generator_pow K n h M aM haM r s ht m

end FLT.Mazur.PolygonInfinitesimalStages

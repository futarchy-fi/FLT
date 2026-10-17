/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothOriginalCoefficient
public import FLT.Mazur.PolygonCompleteSmoothOriginalGeneratorIso
public import FLT.Mazur.PolygonCompleteSmoothFieldCoefficientGenerator
public import FLT.Mazur.CompatibleSubgroupIsoFaithful
public import FLT.Mazur.CompatibleSubgroupBaseChangeCompEq

/-!
# The actual subgroup coefficient square

Faithfulness of the whole-curve inclusion lifts the full DR coefficient square
to equality of the compatible comparisons of the original finite subgroups.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
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
local notation "E" => completeGeneralizedCurve K n h
local notation "eL" => completeSmoothOriginalCurveIso K n h L a ha p q hs
local notation "eM" => completeSmoothOriginalCurveIso K n h M aM haM r s ht
local notation "eLM" => completeFieldCoefficientCurveIso K n h L a ha p q hs M r s ht 0
local notation "d" => GeneralizedEllipticCurve.baseChangeCompEqIso (E) u b v
  (Eq.symm (completeCoefficientSpec_comp K L a M))

local notation "H" => completeOriginalFiniteSubgroup K n h
local notation "cL" => completeSmoothOriginalSubgroupIso K n h L a ha p q hs
local notation "cM" => completeSmoothOriginalSubgroupIso K n h M aM haM r s ht
local notation "cLM" => completeFieldCoefficientSubgroupIso K n h L a ha p q hs M r s ht
local notation "cD" => compatibleBaseChangeCompEq (H) u b v
  (Eq.symm (completeCoefficientSpec_comp K L a M))

/-- The original finite subgroup coefficient square commutes as compatible DR comparisons. -/
theorem completeSmoothOriginalSubgroupIso_coefficient :
    ((cD).trans ((cL).baseChange b)).trans (cLM) = cM := by
  apply CompatibleIso.ext_curve_hom
  change ((cD).curve.hom ≫ ((baseChangeFunctor b).map (cL).curve.hom)) ≫
    (cLM).curve.hom = (cM).curve.hom
  rw [compatibleBaseChangeCompEq_curve, completeSmoothOriginalSubgroupIso_curve,
    completeFieldCoefficientSubgroupIso_curve, completeSmoothOriginalSubgroupIso_curve]
  change ((d).hom ≫ (baseChangeFunctor b).map (eL).inv) ≫ (eLM).hom = (eM).inv
  apply (cancel_epi (eM).hom).mp
  rw [← Category.assoc, ← Category.assoc,
    ← completeSmoothOriginalCurveIso_coefficient K n h L a ha p q hs M r s ht]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
  rw [(baseChangeFunctor b).map_id]
  change (eLM).inv ≫ (𝟙 _) ≫ (eLM).hom = 𝟙 _
  rw [Category.id_comp, Iso.inv_hom_id]

end FLT.Mazur.PolygonInfinitesimalStages

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXZeroNodeOverlap
public import FLT.Mazur.WeierstrassModificationXFullNodeIncidenceBranch

/-!
# Original localized incidence branches on the full start-zero overlap

The punctured slope scheme maps to each actual localized node branch. The
opposite projection translates the parameter by the tangent, cancelling the
original negative translation when mapped back to the exterior slope line.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (a c : K) (ha : IsUnit a)
local notation "P" => SlopeOpen a
local notation "s₁" => PolygonNodeEqualizer.second (fullNodeNormalizedDenominator a c)
local notation "s₂" => PolygonNodeEqualizer.second (fullNodeNormalizedDenominator (-a) c)
local notation "i" => Spec.map (CommRingCat.ofHom (algebraMap K[X] P))
local notation "t" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (aeval (X - C a : K[X]))))

/-- The whole punctured slope line maps to the first unchanged branch localization. -/
def fullNodeSlopeFirstRestriction : Localization.Away s₁ →ₐ[K] P :=
  IsLocalization.Away.liftAlgHom (f := Algebra.algHom K K[X] P) s₁ (by
    rw [fullNodeNormalizedDenominator_second]
    change IsUnit (algebraMap K[X] P (C a⁻¹ * (X + C a)))
    rw [map_mul, map_add]
    have hC (r : K) : algebraMap K[X] P (C r) = algebraMap K P r :=
      (IsScalarTower.algebraMap_apply K K[X] P r).symm
    rw [hC, hC]
    exact ((ha.inv).map (algebraMap K P)).mul (slope_units a).2.1)

/-- The opposite local parameter is the original slope plus its tangent coefficient. -/
def fullNodeSlopeSecondRestriction : Localization.Away s₂ →ₐ[K] P :=
  IsLocalization.Away.liftAlgHom (f := aeval (slopeZ a + algebraMap K P a)) s₂ (by
    rw [fullNodeNormalizedDenominator_second]
    simp only [map_mul, map_add, aeval_C, aeval_X, map_neg, add_neg_cancel_right]
    exact ((ha.neg.inv).map (algebraMap K P)).mul (slope_units a).1)

/-- The first slope restriction retains every polynomial on the localized branch. -/
theorem fullNodeSlopeFirstRestriction_base (p : K[X]) :
    fullNodeSlopeFirstRestriction a c ha (algebraMap K[X] _ p) = algebraMap K[X] P p := by
  rw [fullNodeSlopeFirstRestriction, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The opposite branch restriction retains the full translated polynomial evaluation. -/
theorem fullNodeSlopeSecondRestriction_base (p : K[X]) :
    fullNodeSlopeSecondRestriction a c ha (algebraMap K[X] _ p) =
      aeval (slopeZ a + algebraMap K P a) p := by
  rw [fullNodeSlopeSecondRestriction, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The actual first overlap map to the localized incidence branch. -/
def fullNodeSlopeFirstBranch : Spec (.of P) ⟶ Spec (.of (Localization.Away s₁)) :=
  Spec.map (CommRingCat.ofHom (fullNodeSlopeFirstRestriction a c ha).toRingHom)

/-- The actual second overlap map keeps its own branch denominator. -/
def fullNodeSlopeSecondBranch : Spec (.of P) ⟶ Spec (.of (Localization.Away s₂)) :=
  Spec.map (CommRingCat.ofHom (fullNodeSlopeSecondRestriction a c ha).toRingHom)

/-- The first overlap branch has the unchanged full slope inclusion. -/
@[reassoc] theorem fullNodeSlopeFirstBranch_open :
    fullNodeSlopeFirstBranch a c ha ≫ NodeLocalDescent.branchOpen K s₁ = i := by
  rw [fullNodeSlopeFirstBranch, NodeLocalDescent.branchOpen, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fullNodeSlopeFirstRestriction_base a c ha)

/-- The opposite overlap branch cancels the original negative slope translation. -/
@[reassoc] theorem fullNodeSlopeSecondBranch_open :
    fullNodeSlopeSecondBranch a c ha ≫ NodeLocalDescent.branchOpen K s₂ ≫ t = i := by
  rw [fullNodeSlopeSecondBranch, NodeLocalDescent.branchOpen, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    change fullNodeSlopeSecondRestriction a c ha
      (algebraMap K[X] _ (aeval (X - C a) (C r))) = algebraMap K[X] P (C r)
    rw [aeval_C, fullNodeSlopeSecondRestriction_base, AlgHom.commutes]
    exact IsScalarTower.algebraMap_apply K K[X] P r
  · change fullNodeSlopeSecondRestriction a c ha
      (algebraMap K[X] _ (aeval (X - C a) X)) = algebraMap K[X] P X
    rw [aeval_X, fullNodeSlopeSecondRestriction_base]
    simp only [map_sub, aeval_X, aeval_C, add_sub_cancel_right, slopeZ]

variable (hc : c = 0)

/-- The first categorical overlap projection is the original incidence branch restriction. -/
theorem fullZeroNodeOverlapFirst_branch :
    fullZeroNodeOverlapFirst a c ha hc =
      fullNodeSlopeFirstBranch a c ha ≫ fullNodeSecondBranch a c ha := by
  apply (cancel_mono (fullFirstNodeChart a c ha)).mp
  rw [fullZeroNodeOverlapFirst_global, Category.assoc, fullNodeSecondBranch_firstChart,
    fullNodeSlopeFirstBranch_open_assoc, fiberExteriorSlopeChart_incidence]

/-- The opposite categorical projection retains the branch's original negative translation. -/
theorem fullZeroNodeOverlapSecond_branch :
    fullZeroNodeOverlapSecond a c ha hc =
      fullNodeSlopeSecondBranch a c ha ≫ fullNodeSecondBranch (-a) c ha.neg := by
  apply (cancel_mono (fullSecondNodeChart a c ha)).mp
  rw [fullZeroNodeOverlapSecond_global, Category.assoc, fullNodeSecondBranch_secondChart,
    fullNodeSlopeSecondBranch_open_assoc, fiberExteriorSlopeChart_incidence]

include hc in
/-- Equal original exterior restrictions give equality on the full scheme overlap. -/
theorem fullZeroNodeMaps_compatible {Y : Scheme.{u}}
    (d₁ : Spec (.of (FullNodeOpen a c)) ⟶ Y)
    (d₂ : Spec (.of (FullNodeOpen (-a) c)) ⟶ Y) (g : ProjectiveLine.chart K ⟶ Y)
    (h₁ : fullNodeSecondBranch a c ha ≫ d₁ = NodeLocalDescent.branchOpen K s₁ ≫ g)
    (h₂ : fullNodeSecondBranch (-a) c ha.neg ≫ d₂ =
      NodeLocalDescent.branchOpen K s₂ ≫ t ≫ g) :
    pullback.fst (fullFirstNodeChart a c ha) (fullSecondNodeChart a c ha) ≫ d₁ =
      pullback.snd (fullFirstNodeChart a c ha) (fullSecondNodeChart a c ha) ≫ d₂ := by
  apply (cancel_epi (fullZeroNodeOverlapIso a c ha hc).hom).mp
  simp only [← Category.assoc]
  change fullZeroNodeOverlapFirst a c ha hc ≫ d₁ = fullZeroNodeOverlapSecond a c ha hc ≫ d₂
  rw [fullZeroNodeOverlapFirst_branch, fullZeroNodeOverlapSecond_branch,
    Category.assoc, Category.assoc, h₁, h₂,
    fullNodeSlopeFirstBranch_open_assoc, fullNodeSlopeSecondBranch_open_assoc]

end FLT.Mazur.WeierstrassModificationX

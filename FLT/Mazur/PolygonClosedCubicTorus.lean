/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonClosedCubicContractionIso
public import FLT.Mazur.CartesianFiniteFibers

/-!
# The full retained torus of the original closed cubic

The global one-gon comparison carries the complete Laurent open to an
unchanged open of the original closed cubic, with its original polygon map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching PolygonOneGonContraction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completeClosedFiberInclusion completePointToIntegralCubic

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hp" => PolygonCyclicPushout.isPushout K n h (by omega)
local notation "E" => closedPointContractionCubicIso K n h i
local notation "g" => closedPointToCubic K n h i
local notation "t" => Over.Hom.left (torusToComponent K ≫ componentι K n i ≫ p)

/-- The complete Laurent chart on the actual original closed cubic. -/
def closedPointCubicTorus :
    (MultiplicativeGroupScheme.gm K).left ⟶ (closedPointCubicOver K n h i).left :=
  (PolygonAtlas.torus K 1 0).left ≫ (E).hom

instance closedPointCubicTorus_open : IsOpenImmersion (closedPointCubicTorus K n h i) := by
  unfold closedPointCubicTorus
  infer_instance

/-- The original retained Laurent inclusion is the entire inverse image of the cubic torus. -/
theorem closedPointCubicTorus_isPullback :
    IsPullback (𝟙 (MultiplicativeGroupScheme.gm K).left) (t)
      (closedPointCubicTorus K n h i) (g) := by
  exact (contraction_torus_square K n (by omega) p q hp i).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (E)
    (by simp) (by simp) (by simp [closedPointCubicTorus])
    (by simpa only [Iso.refl_hom, Category.id_comp, closedPointContraction] using
      closedPointContractionCubicIso_fac K n h i)

/-- The unchanged closed-fiber torus is the full original Laurent open. -/
theorem closedPointCubicTorus_isIso :
    IsIso ((g) ∣_ (closedPointCubicTorus K n h i).opensRange) :=
  SchemeUnchangedOpen.isIso_of_identity_pullback (g) _ _
    (closedPointCubicTorus_isPullback K n h i)

/-- Every point on this actual cubic torus has a finite original closed-polygon fiber. -/
theorem closedPointCubicTorus_finite_fiber (y : (closedPointCubicOver K n h i).left)
    (hy : y ∈ (closedPointCubicTorus K n h i).opensRange) :
    ((g) ⁻¹' {y}).Finite := by
  let _ := closedPointCubicTorus_isIso K n h i
  exact CartesianFiniteFibers.finite_fiber_of_restrict_isIso (g) _ y hy

end FLT.Mazur.PolygonInfinitesimalStages

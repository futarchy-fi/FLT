/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralCoordinateEquations
public import FLT.Mazur.WeierstrassDividedGlobalFiniteStep
public import FLT.Mazur.ModulePullbackStageGlobalSections

/-!
# Original coordinates on every actual divided projective model

The existing contraction constructs the coordinate line and its three sections
on the original resolved models. Their equations and compatibility with every
resolution step are proved; they are not input coordinate data.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.WeierstrassDividedDepth
open FCurve WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)

/-- The original cubic coordinate line on the actual divided global model. -/
def finiteGlobalCoordinateLine : (finiteGlobalModel hπ data j hj).Modules :=
  (pullback (finiteGlobalContraction hπ data j hj)).obj (integralCoordinateLine W)

/-- Actual original homogeneous sections on the divided model. -/
def finiteGlobalCoordinateSection (i : Fin 3) : Γ(finiteGlobalCoordinateLine hπ data j hj, ⊤) :=
  pullGlobal (finiteGlobalContraction hπ data j hj) (integralCoordinateLine W)
    (integralCoordinateSection W i)

/-- The original coordinate line remains locally free on every exceptional component. -/
theorem finiteGlobalCoordinateLine_locallyFreeRankOne :
    LocallyFreeRankOne (finiteGlobalCoordinateLine hπ data j hj) :=
  (integralCoordinateLine_locallyFreeRankOne W).pullback _

/-- The original coordinates generate everywhere, including over the exceptional locus. -/
theorem finiteGlobalCoordinateSections_cover :
    (⨆ i, sectionGeneratorOpen (finiteGlobalCoordinateLine hπ data j hj)
      (finiteGlobalCoordinateSection hπ data j hj i)) = ⊤ :=
  sectionGeneratorCover_pullback _ _ (integralCoordinateLine_locallyFreeRankOne W) 2
    (integralCoordinateSection W) (integralCoordinateSections_cover W)

/-- All normalized equations use the original structural coefficient morphism. -/
theorem finiteGlobalCoordinateSections_equations :
    CubicCoordinateEquations (finiteGlobalCoordinateLine hπ data j hj) W
      (finiteGlobalCoordinateSection hπ data j hj)
      ((finiteGlobalStructure hπ data j hj).appTop.hom.comp
        (Scheme.ΓSpecIso (.of R)).inv.hom) := by
  have he := integralCoordinateSections_pullback_equations W
    (finiteGlobalContraction hπ data j hj)
  exact he

/-- Each original affine coordinate open pulls back to its precise generator locus. -/
theorem finiteGlobalCoordinateSection_generatorOpen (i : Fin 3) :
    sectionGeneratorOpen (finiteGlobalCoordinateLine hπ data j hj)
      (finiteGlobalCoordinateSection hπ data j hj i) =
      finiteGlobalContraction hπ data j hj ⁻¹ᵁ (integralCurveChart W i).opensRange := by
  change sectionGeneratorOpen ((pullback _).obj (integralCoordinateLine W))
    (pullGlobal _ (integralCoordinateLine W) (integralCoordinateSection W i)) = _
  rw [sectionGeneratorOpen_pullGlobal (integralCoordinateLine_locallyFreeRankOne W),
    integralCoordinateSection_generatorOpen]

variable (hs : j + 1 ≤ n)

/-- The actual resolution step identifies the two original coordinate lines. -/
def finiteGlobalCoordinateStepIso :
    (pullback (finiteGlobalStep hπ data j hs)).obj
      (finiteGlobalCoordinateLine hπ data j (Nat.le_of_succ_le hs)) ≅
        finiteGlobalCoordinateLine hπ data (j + 1) hs :=
  pullbackStageIso _ _ _ (finiteGlobalStep_contraction hπ data j hs) (integralCoordinateLine W)

/-- Every original coordinate is retained under an actual resolution step. -/
theorem finiteGlobalCoordinateSection_step (i : Fin 3) :
    (finiteGlobalCoordinateStepIso hπ data j hs).hom.app ⊤
      (pullGlobal (finiteGlobalStep hπ data j hs) _
        (finiteGlobalCoordinateSection hπ data j (Nat.le_of_succ_le hs) i)) =
      finiteGlobalCoordinateSection hπ data (j + 1) hs i :=
  pullbackStageIso_globalSection _ _ _ (finiteGlobalStep_contraction hπ data j hs)
    (integralCoordinateLine W) (integralCoordinateSection W i)

end FLT.Mazur.WeierstrassDividedDepth

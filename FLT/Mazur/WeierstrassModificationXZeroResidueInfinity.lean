/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXZeroResidueGeometry
public import FLT.Mazur.WeierstrassProductOverlap
public import FLT.Mazur.WeierstrassIntegralCurveMorphisms

/-!
# The original infinity transition on the whole start-zero slope chart

The cubic vertical function is invertible on the entire slope chart. The
original Y/Z transition therefore extends across the whole chart, retaining
the full affine restriction and the original projective cubic contraction.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth) (k : ℕ) (hk : k = 0) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)
open WeierstrassIntegralChart
local notation "a" => residue R W.a₁
local notation "P" => SlopeOpen a
local notation "original" => zeroResidueOriginalMap D hdepth k hk b3 b4 b6 h3 h4 h6

/-- The original cubic Y coordinate is a unit on every point of the slope chart. -/
theorem zeroResidueOriginalMap_y_isUnit : IsUnit (original (coord W 2 1)) := by
  rw [zeroResidueOriginalMap_y]
  exact ((slope_units a).1.mul (slope_units a).2.1).mul (slope_units a).1

/-- The entire original affine Y-boundary maps to the slope chart. -/
def zeroResidueBoundaryMap : Overlap W 2 1 →ₐ[R] P :=
  overlapLift W 2 1 original (zeroResidueOriginalMap_y_isUnit D hdepth k hk b3 b4 b6 h3 h4 h6)

/-- All original affine functions retain their restrictions to the full Y-boundary. -/
theorem zeroResidueBoundaryMap_restriction :
    (zeroResidueBoundaryMap D hdepth k hk b3 b4 b6 h3 h4 h6).comp
      (overlapRestriction W 2 1) = original :=
  overlapLift_restriction W 2 1 original _

/-- The original infinity-coordinate map on the whole slope chart. -/
def zeroResidueInfinityMap : WeierstrassIntegralChart.Coordinate W 1 →ₐ[R] P :=
  (zeroResidueBoundaryMap D hdepth k hk b3 b4 b6 h3 h4 h6).comp (transitionBase W 2 1)

/-- The whole slope chart maps into the original infinity chart. -/
def zeroResidueToInfinity : Spec (.of P) ⟶ chartScheme W 1 :=
  Spec.map (CommRingCat.ofHom
    (zeroResidueInfinityMap D hdepth k hk b3 b4 b6 h3 h4 h6).toRingHom)

/-- The infinity transition retains precisely the original projective cubic contraction. -/
@[reassoc] theorem zeroResidueToInfinity_contraction :
    zeroResidueToInfinity D hdepth k hk b3 b4 b6 h3 h4 h6 ≫ integralCurveChart W 1 =
      zeroResidueSlopeContraction D hdepth k hk b3 b4 b6 h3 h4 h6 := by
  change Spec.map (CommRingCat.ofHom ((zeroResidueBoundaryMap
    D hdepth k hk b3 b4 b6 h3 h4 h6).comp (transitionBase W 2 1)).toRingHom) ≫ _ = _
  rw [show CommRingCat.ofHom ((zeroResidueBoundaryMap
      D hdepth k hk b3 b4 b6 h3 h4 h6).comp (transitionBase W 2 1)).toRingHom =
      CommRingCat.ofHom (transitionBase W 2 1).toRingHom ≫
        CommRingCat.ofHom (zeroResidueBoundaryMap
          D hdepth k hk b3 b4 b6 h3 h4 h6).toRingHom from rfl]
  rw [Spec.map_comp, Category.assoc, integralCurve_output_transition, ← Category.assoc]
  change (Spec.map _ ≫ Spec.map _) ≫ _ = _
  rw [← Spec.map_comp]
  have h := congrArg (fun f : WeierstrassIntegralChart.Coordinate W 2 →ₐ[R] P =>
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ integralCurveChart W 2)
    (zeroResidueBoundaryMap_restriction D hdepth k hk b3 b4 b6 h3 h4 h6)
  exact h

end FLT.Mazur.WeierstrassModificationX

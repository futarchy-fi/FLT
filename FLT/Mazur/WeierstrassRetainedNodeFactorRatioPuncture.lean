/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedNodeFactorRatioBoundary
public import FLT.Mazur.WeierstrassModificationXFactorRatioLaurentEquiv
public import FLT.Mazur.NodalFiberZeroTangentMobiusPuncture

/-!
# The retained comparison on the full original right puncture

The actual right branch of the source node maps by the original corrected
Laurent isomorphism followed by cyclic inversion and the target right branch.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (π s c3 c4 c6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁)
  (hs : s ∈ I) (h2 : W.a₂ ∈ I) (h3 : c3 ∈ I) (h4 : c4 ∈ I) (h6 : c6 ∈ I)
  (d : R) (hd : s = π * d)
local notation "τ" => initialTangentSmoothing W ha s
local notation "F" => retainedFactorRatioEvaluation W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 d hd
local notation "u" => factorRatioLaurentUnit W ha s (π * c3) (π * c4) (π ^ 2 * c6)
  I hI hs h2 (I.mul_mem_left π h3) (I.mul_mem_left π h4) (I.mul_mem_left (π ^ 2) h6)
local notation "E" => factorRatioLaurentIso W ha s (π * c3) (π * c4) (π ^ 2 * c6)
  I hI hs h2 (I.mul_mem_left π h3) (I.mul_mem_left π h4) (I.mul_mem_left (π ^ 2) h6)
attribute [local irreducible] retainedFactorRatioEvaluation factorRatioLaurentUnit

/-- The original retained right puncture is the spectrum of the full Laurent evaluation. -/
theorem retainedRightEvaluation_spec :
    Spec.map (CommRingCat.ofHom (retainedRightEvaluation π).toRingHom) =
      rightBranchOpen R π := by
  rw [rightBranchOpen_eq_spec]
  rfl

/-- The retained map has the entire original reciprocal Laurent boundary. -/
@[reassoc] theorem retainedFactorRatioChart_right_boundary :
    rightBranchOpen R π ≫
      retainedFactorRatioChart W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 d hd =
        (E).hom ≫ (edgeInversion R).hom ≫ rightBranchOpen R τ := by
  rw [← retainedRightEvaluation_spec, retainedFactorRatioChart, ← Spec.map_comp]
  have h := boundary_rightBranchOpen τ ((retainedRightEvaluation π).comp F) (u)⁻¹
    (retainedFactorRatioEvaluation_right_boundary W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6
      d hd)
  rw [NodalFiber.unitParameter_inverse, Category.assoc] at h
  exact h

/-- Inverting the full Laurent isomorphism recovers the original preceding target edge. -/
@[reassoc] theorem retainedFactorRatioChart_inv_right_boundary :
    (E).inv ≫ rightBranchOpen R π ≫
      retainedFactorRatioChart W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 d hd =
        precedingBranch R τ := by
  rw [retainedFactorRatioChart_right_boundary, Iso.inv_hom_id_assoc]
  rfl

end FLT.Mazur.WeierstrassModificationX

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingFramedProducts
public import FLT.Mazur.CurveStructureEuler
public import FLT.Mazur.NodalGeometricFiberGenus

/-!
# Original geometric fibers over the affine coefficient spectrum

Replacing an affine base by its canonical spectrum changes neither the actual
Cartesian geometric fiber nor its dimension and structure Euler characteristic.
These computations use the original generalized curve's genus-one condition.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme} [IsAffine S] (E : GeneralizedEllipticCurve S)
  {K : Type} [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ Spec Γ(S, ⊤))

local instance generalizedCurveCoefficientGeometricFiberProper :
    IsProper E.curve.hom := E.family.family.1

omit [IsAlgClosed K] in
/-- The coefficient-spectrum fiber is also the original scheme-base fiber. -/
theorem coefficientGeometricFiber_isPullback :
    IsPullback (pullback.fst (E.curve.hom ≫ S.toSpecΓ) b)
      (pullback.snd (E.curve.hom ≫ S.toSpecΓ) b) E.curve.hom (b ≫ S.isoSpec.inv) := by
  apply IsPullback.of_bot (h₃₁ := b) _ _
    (IsPullback.of_vert_isIso (fst := b ≫ S.isoSpec.inv) (snd := 𝟙 _)
      (f := S.toSpecΓ) ⟨by simp [← Scheme.isoSpec_hom]⟩)
  · simpa using (IsPullback.of_hasPullback (E.curve.hom ≫ S.toSpecΓ) b)
  · rw [← cancel_mono S.toSpecΓ]
    simp only [Category.assoc, Scheme.isoSpec_inv_toSpecΓ, Category.comp_id]
    exact pullback.condition

/-- The original coefficient-spectrum geometric fiber has dimension one. -/
theorem coefficientGeometricFiber_dimension :
    topologicalKrullDim (pullback (E.curve.hom ≫ S.toSpecΓ) b : Scheme) = 1 :=
  (E.family.genus.fiber K (b ≫ S.isoSpec.inv) _ _
    (E.coefficientGeometricFiber_isPullback b)).toNodalFiberCore.topologicalKrullDim_eq_one

/-- The original coefficient-spectrum geometric fiber has zero structure Euler characteristic. -/
theorem coefficientGeometricFiber_euler :
    curveEulerCharacteristic (pullback.snd (E.curve.hom ≫ S.toSpecΓ) b)
      (structureModule (pullback (E.curve.hom ≫ S.toSpecΓ) b)) = 0 := by
  have h := E.family.genus.fiber K (b ≫ S.isoSpec.inv) _ _
    (E.coefficientGeometricFiber_isPullback b)
  apply curveEulerCharacteristic_structure_zero
  · exact finrank_H0_of_constantGlobalSections _ h.constantSections
  · exact h.genus_one

end FLT.Mazur.GeneralizedEllipticCurve

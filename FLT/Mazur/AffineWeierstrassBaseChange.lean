/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassIntegralBaseChange
public import FLT.Mazur.WeierstrassCoefficientZero

/-!
# Coefficient presentations over original affine bases

Changing the five coefficients along an actual affine scheme morphism
presents the categorical base change, retaining infinity. Both affine
bases may be non-Noetherian, nonreduced and of mixed characteristic.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {U T : Scheme} [IsAffine U] [IsAffine T]
  (W : WeierstrassCurve Γ(U, ⊤)) (h : T ⟶ U)

/-- The integral cubic structure morphism over its actual affine scheme base. -/
def affineIntegralStructure : integralCurve W ⟶ U := integralCurveStructure W ≫ U.isoSpec.inv

/-- Infinity over the actual affine base. -/
def affineIntegralZero : U ⟶ integralCurve W := U.toSpecΓ ≫ integralCurveZero W

/-- Infinity remains a section before passing to coefficient spectra. -/
@[reassoc] theorem affineIntegralZero_over :
    affineIntegralZero W ≫ affineIntegralStructure W = 𝟙 U := by
  rw [affineIntegralZero, affineIntegralStructure, Category.assoc,
    ← Category.assoc (integralCurveZero W), integralCurveZero_structure, Category.id_comp]
  exact U.isoSpec.hom_inv_id

/-- The actual coefficient projection for an arbitrary affine base morphism. -/
def affineIntegralCoefficient : integralCurve (W.map h.appTop.hom) ⟶ integralCurve W := by
  let _ := h.appTop.hom.toAlgebra
  exact integralCoefficientMorphism W

/-- Extending coefficients presents the actual categorical base change of the whole cubic. -/
theorem affineIntegralCoefficient_isPullback :
    IsPullback (affineIntegralCoefficient W h)
      (affineIntegralStructure (W.map h.appTop.hom)) (affineIntegralStructure W) h := by
  let _ := h.appTop.hom.toAlgebra
  refine (integralCoefficient_isPullback (S := Γ(T, ⊤)) W).of_iso
    (Iso.refl _) (Iso.refl _) T.isoSpec.symm U.isoSpec.symm
    (by simp [affineIntegralCoefficient])
    (by simp only [affineIntegralStructure, Iso.refl_hom, Iso.symm_hom, Category.id_comp];
        rfl) (by simp [affineIntegralStructure]) ?_
  exact Scheme.isoSpec_inv_naturality h

omit [IsAffine U] [IsAffine T] in
/-- The coefficient projection retains the actual affine infinity sections. -/
@[reassoc] theorem affineIntegralCoefficient_zero :
    affineIntegralZero (W.map h.appTop.hom) ≫ affineIntegralCoefficient W h =
      h ≫ affineIntegralZero W := by
  let _ := h.appTop.hom.toAlgebra
  change (T.toSpecΓ ≫ integralCurveZero (W.map (algebraMap Γ(U, ⊤) Γ(T, ⊤)))) ≫
    integralCoefficientMorphism W = h ≫ U.toSpecΓ ≫ integralCurveZero W
  rw [Category.assoc, integralCoefficientMorphism_zero (S := Γ(T, ⊤)) W]
  change T.toSpecΓ ≫ Spec.map h.appTop ≫ integralCurveZero W = _
  rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc]

/-- The actual equation over the changed ring is a presentation of the categorical pullback. -/
def affineIntegralBaseChangeIso : integralCurve (W.map h.appTop.hom) ≅
    Limits.pullback (affineIntegralStructure W) h :=
  (affineIntegralCoefficient_isPullback W h).isoPullback

/-- This presentation retains the coefficient projection. -/
@[reassoc] theorem affineIntegralBaseChangeIso_fst :
    (affineIntegralBaseChangeIso W h).hom ≫ Limits.pullback.fst _ _ =
      affineIntegralCoefficient W h := IsPullback.isoPullback_hom_fst _

/-- This presentation retains the original changed base. -/
@[reassoc] theorem affineIntegralBaseChangeIso_snd :
    (affineIntegralBaseChangeIso W h).hom ≫ Limits.pullback.snd _ _ =
      affineIntegralStructure (W.map h.appTop.hom) := IsPullback.isoPullback_hom_snd _

end FLT.Mazur.WeierstrassIntegralChart

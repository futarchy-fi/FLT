/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineGeometricOverlap

/-!
# Recovering overlap-ring linearity from both tensor scalar actions

A tensor isomorphism linear for the first copy of `S` and respecting the
second copy gives an isomorphism of section modules over `S ⊗[R] S`.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricOverlap
open AffineOverlapTensor AffineOverlapPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
attribute [local instance] AffineOverlapPullback.instModuleCarrierCarrierOfCoefficients
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
variable (e : coefficients S M ⊗[R] S ≃ₗ[S] S ⊗[R] coefficients S M)
variable (he : ∀ (n : coefficients S M) (s t : S), e (n ⊗ₜ[R] (s * t)) =
  (Algebra.lsmul R R (coefficients S M) s).lTensor S (e (n ⊗ₜ[R] t)))

/-- Convert a tensor isomorphism to an additive isomorphism of actual section modules. -/
def sectionsAddEquiv :
    moduleSpecΓFunctor.obj ((pullback (Spec.map (CommRingCat.ofHom (left R S)))).obj M) ≃+
      moduleSpecΓFunctor.obj ((pullback (Spec.map (CommRingCat.ofHom (right R S)))).obj M) :=
  (firstSections R S M).symm.trans (e.toAddEquiv.trans (secondSections R S M))

/-- The converted section isomorphism agrees with the original tensor map. -/
theorem sectionsAddEquiv_first (x : coefficients S M ⊗[R] S) :
    sectionsAddEquiv R S M e (firstSections R S M x) = secondSections R S M (e x) := by
  exact congrArg (fun y ↦ secondSections R S M (e y))
    ((firstSections R S M).symm_apply_apply x)

include he

/-- The two scalar laws imply overlap-ring linearity on pure tensors. -/
theorem sectionsAddEquiv_smul_tmul (a b t : S) (n : coefficients S M) :
    sectionsAddEquiv R S M e ((a ⊗ₜ[R] b) • firstSections R S M (n ⊗ₜ[R] t)) =
      (a ⊗ₜ[R] b) • sectionsAddEquiv R S M e (firstSections R S M (n ⊗ₜ[R] t)) := by
  rw [← firstSections_smul_tmul, sectionsAddEquiv_first, sectionsAddEquiv_first,
    ← smul_tmul', e.map_smul, he, secondSections_smul, secondSections_other_smul,
    smul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Tensor induction extends the two scalar laws to the complete overlap-ring action. -/
theorem sectionsAddEquiv_smul (c : S ⊗[R] S)
    (x : moduleSpecΓFunctor.obj
      ((pullback (Spec.map (CommRingCat.ofHom (left R S)))).obj M)) :
    sectionsAddEquiv R S M e (c • x) = c • sectionsAddEquiv R S M e x := by
  obtain ⟨y, rfl⟩ := (firstSections R S M).surjective x
  induction c using TensorProduct.inductionOn with
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | tmul n t => exact sectionsAddEquiv_smul_tmul R S M e he a b t n
    | add y z hy hz => simp only [map_add, smul_add, hy, hz]
  | add c d hc hd => simp only [add_smul, map_add, hc, hd]

set_option maxRecDepth 2048 in
/-- The tensor map, with its two scalar laws, is linear over the whole overlap ring. -/
def sectionsLinearEquiv :
    moduleSpecΓFunctor.obj ((pullback (Spec.map (CommRingCat.ofHom (left R S)))).obj M) ≃ₗ[S ⊗[R] S]
      moduleSpecΓFunctor.obj ((pullback (Spec.map (CommRingCat.ofHom (right R S)))).obj M) :=
  { sectionsAddEquiv R S M e with map_smul' := sectionsAddEquiv_smul R S M e he }

/-- Bundle the recovered overlap-ring linear equivalence in the category of modules. -/
def sectionsIso :
    moduleSpecΓFunctor.obj ((pullback (Spec.map (CommRingCat.ofHom (left R S)))).obj M) ≅
      moduleSpecΓFunctor.obj ((pullback (Spec.map (CommRingCat.ofHom (right R S)))).obj M) :=
  (sectionsLinearEquiv R S M e he).toModuleIso

/-- The bundled isomorphism has the prescribed tensor-coordinate action. -/
theorem sectionsIso_first (x : coefficients S M ⊗[R] S) :
    (sectionsIso R S M e he).hom (firstSections R S M x) =
      secondSections R S M (e x) :=
  sectionsAddEquiv_first R S M e x

end FLT.Mazur.AffineGeometricOverlap

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTripleOverlapPullback

/-!
# Direct coefficients for the third affine projection

Rotate the last scalar into the first position before cancelling scalar
extension. The resulting chart uses the direct third-coordinate pullback,
and evaluates pure tensors without an iterated sheaf comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
open scoped ChangeOfRings
universe u
namespace FLT.Mazur.AffineDirectTripleSections
open AffineOverlapTensor AffineOverlapPullback AffineTripleOverlapMaps AffineTripleOverlapPullback
open AffineIteratedPullbackSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Move the third scalar to the first coordinate. -/
def rotate : Triple R S ≃ₐ[R] Triple R S :=
  (Algebra.TensorProduct.assoc R R R S S S).symm.trans
    (Algebra.TensorProduct.comm R (S ⊗[R] S) S)

@[simp] theorem rotate_tmul (a b c : S) :
    rotate R S (a ⊗ₜ[R] (b ⊗ₜ[R] c)) = c ⊗ₜ[R] (a ⊗ₜ[R] b) := rfl
@[simp] theorem rotate_symm_tmul (a b c : S) :
    (rotate R S).symm (a ⊗ₜ[R] (b ⊗ₜ[R] c)) = b ⊗ₜ[R] (c ⊗ₜ[R] a) := rfl

/-- Rotation identifies the restricted last-coordinate action with the first action. -/
def swapScalars :
    (ModuleCat.restrictScalars (coord3 R S)).obj
      (ModuleCat.of (Triple R S) (Triple R S)) ≃ₗ[S] Triple R S where
  toFun := rotate R S
  invFun := (rotate R S).symm
  map_add' := map_add _
  map_smul' t x := by
    change rotate R S (((1 : S) ⊗ₜ[R] ((1 : S) ⊗ₜ[R] t)) * (show Triple R S from x)) = _
    rw [map_mul, rotate_tmul]
    exact (Algebra.smul_def (A := Triple R S) t (rotate R S x)).symm
  left_inv := (rotate R S).left_inv
  right_inv := (rotate R S).right_inv

variable (N : Type u) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
/-- Cancel extension of scalars along the third coordinate inclusion. -/
def extension :
    ((ModuleCat.extendScalars (coord3 R S)).obj (ModuleCat.of S N)) ≃+
      S ⊗[R] (S ⊗[R] N) :=
  ((TensorProduct.congr (swapScalars R S) (LinearEquiv.refl S N) ≪≫ₗ
    TensorProduct.comm S (Triple R S) N ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange R S S N (S ⊗[R] S)).toAddEquiv.trans
        (TensorProduct.comm R N (S ⊗[R] S)).toAddEquiv).trans
          (TensorProduct.assoc R S S N).toAddEquiv

@[simp] theorem extension_tmul (a b c : S) (n : N) :
    extension R S N ((a ⊗ₜ[R] (b ⊗ₜ[R] c)) ⊗ₜ[S,coord3 R S] n) =
      a ⊗ₜ[R] (b ⊗ₜ[R] (c • n)) := rfl

@[simp] theorem extension_symm_tmul (a b : S) (n : N) :
    (extension R S N).symm (a ⊗ₜ[R] (b ⊗ₜ[R] n)) =
      (a ⊗ₜ[R] (b ⊗ₜ[R] (1 : S))) ⊗ₜ[S,coord3 R S] n := rfl

variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]
/-- Restrict coefficient scalars to the base ring. -/
local instance : Module R (coefficients S M) := Module.compHom _ (algebraMap R S)
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
/-- An injective chart for coefficients of the actual third-coordinate pullback. -/
def directSections : S ⊗[R] (S ⊗[R] coefficients S M) ≃+
    moduleSpecΓFunctor.obj (coordinate R S M (coord3 R S)) :=
  (extension R S (coefficients S M)).symm.trans
    (AffineModulePullbackSections.sectionsIso
      (CommRingCat.ofHom (coord3 R S)) M).toLinearEquiv.toAddEquiv

/-- Pure tensors are scalar multiples of the direct pullback unit. -/
theorem directSections_tmul (a b : S) (n : coefficients S M) :
    directSections R S M (a ⊗ₜ[R] (b ⊗ₜ[R] n)) =
      (a ⊗ₜ[R] (b ⊗ₜ[R] (1 : S))) • specUnit (CommRingCat.ofHom (coord3 R S)) M n :=
  AffineModulePullbackSections.sectionsIso_tmul (CommRingCat.ofHom (coord3 R S)) M _ n
end FLT.Mazur.AffineDirectTripleSections

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModulePullbackSections
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Coefficients of projections with unequal affine factors

For two algebras `S` and `T`, the coefficients of the second projection
pullback of a sheaf on `Spec T` are `S ⊗[R] N`. Allowing unequal factors
makes this comparison applicable to the triple overlap.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
open scoped ChangeOfRings
universe u
namespace FLT.Mazur.AffinePairPullbackSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- The second inclusion for two possibly different affine factors. -/
abbrev inclusion : T →+* S ⊗[R] T :=
  ↑(Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T)

/-- Swapping the two factors places the restricted scalar on the first factor. -/
def swapScalars :
    (ModuleCat.restrictScalars (inclusion R S T)).obj
      (ModuleCat.of (S ⊗[R] T) (S ⊗[R] T)) ≃ₗ[T] T ⊗[R] S where
  toFun := Algebra.TensorProduct.comm R S T
  invFun := Algebra.TensorProduct.comm R T S
  map_add' := map_add _
  map_smul' t x := by
    exact (map_mul (Algebra.TensorProduct.comm R S T) ((1 : S) ⊗ₜ[R] t) x).trans
      (Algebra.smul_def (A := T ⊗[R] S) t (Algebra.TensorProduct.comm R S T x)).symm
  left_inv := (Algebra.TensorProduct.comm R S T).left_inv
  right_inv := (Algebra.TensorProduct.comm R S T).right_inv

variable (N : Type u) [AddCommGroup N] [Module R N] [Module T N] [IsScalarTower R T N]

/-- Cancel scalar extension along the second projection. -/
def extension :
    ((ModuleCat.extendScalars (inclusion R S T)).obj (ModuleCat.of T N)) ≃+ S ⊗[R] N :=
  (TensorProduct.congr (swapScalars R S T) (LinearEquiv.refl T N) ≪≫ₗ
    TensorProduct.comm T (T ⊗[R] S) N ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange R T T N S).toAddEquiv.trans
        (TensorProduct.comm R N S).toAddEquiv

@[simp]
theorem extension_tmul (s : S) (t : T) (n : N) :
    extension R S T N ((s ⊗ₜ[R] t) ⊗ₜ[T,inclusion R S T] n) = s ⊗ₜ[R] (t • n) := rfl

@[simp]
theorem extension_symm_tmul (s : S) (n : N) :
    (extension R S T N).symm (s ⊗ₜ[R] n) = (s ⊗ₜ[R] 1) ⊗ₜ[T,inclusion R S T] n := rfl

/-- The coefficient comparison preserves the full tensor-ring action. -/
theorem extension_symm_smul_tmul (a s : S) (b : T) (n : N) :
    (a ⊗ₜ[R] b) • (extension R S T N).symm (s ⊗ₜ[R] n) =
      (extension R S T N).symm ((a * s) ⊗ₜ[R] (b • n)) := by
  change ((a ⊗ₜ[R] b) * (s ⊗ₜ[R] (1 : T))) ⊗ₜ[T,inclusion R S T] n =
    ((a * s) ⊗ₜ[R] (1 : T)) ⊗ₜ[T,inclusion R S T] (b • n)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [← smul_tmul (R := T) (M := (ModuleCat.restrictScalars (inclusion R S T)).obj
    (ModuleCat.of (S ⊗[R] T) (S ⊗[R] T)))]
  change ((a * s) ⊗ₜ[R] b) ⊗ₜ[T,inclusion R S T] n =
    (((1 : S) ⊗ₜ[R] b) * ((a * s) ⊗ₜ[R] (1 : T))) ⊗ₜ[T,inclusion R S T] n
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

variable (M : (Spec (.of T)).Modules) [M.IsQuasicoherent]
/-- Restrict coefficient scalars to the common base ring. -/
local instance coefficientModule : Module R (moduleSpecΓFunctor.obj M) :=
  Module.compHom _ (algebraMap R T)
local instance : IsScalarTower R T (moduleSpecΓFunctor.obj M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

/-- Sections of the actual second-projection pullback for unequal factors. -/
def sections : S ⊗[R] moduleSpecΓFunctor.obj M ≃+
    moduleSpecΓFunctor.obj ((pullback (Spec.map (CommRingCat.ofHom (inclusion R S T)))).obj M) :=
  (extension R S T (moduleSpecΓFunctor.obj M)).symm.trans
    (AffineModulePullbackSections.sectionsIso
      (CommRingCat.ofHom (inclusion R S T)) M).toLinearEquiv.toAddEquiv

/-- Pure tensors correspond to scalar multiples of the actual pullback unit. -/
theorem sections_tmul (s : S) (n : moduleSpecΓFunctor.obj M) :
    sections R S T M (s ⊗ₜ[R] n) =
      (s ⊗ₜ[R] (1 : T)) • (show moduleSpecΓFunctor.obj
        ((pullback (Spec.map (CommRingCat.ofHom (inclusion R S T)))).obj M) from
        ((pullbackPushforwardAdjunction (Spec.map (CommRingCat.ofHom (inclusion R S T)))).unit.app
          M).app ⊤ n) :=
  AffineModulePullbackSections.sectionsIso_tmul
    (CommRingCat.ofHom (inclusion R S T)) M _ n

/-- Both affine factors act as prescribed on the projection coefficients. -/
theorem sections_smul_tmul (a s : S) (b : T) (n : moduleSpecΓFunctor.obj M) :
    sections R S T M ((a * s) ⊗ₜ[R] (b • n)) =
      (a ⊗ₜ[R] b) • sections R S T M (s ⊗ₜ[R] n) := by
  change (AffineModulePullbackSections.sectionsIso
    (CommRingCat.ofHom (inclusion R S T)) M).hom _ =
      (a ⊗ₜ[R] b) • (AffineModulePullbackSections.sectionsIso
        (CommRingCat.ofHom (inclusion R S T)) M).hom _
  exact (congrArg (AffineModulePullbackSections.sectionsIso
    (CommRingCat.ofHom (inclusion R S T)) M).hom
      (extension_symm_smul_tmul R S T (moduleSpecΓFunctor.obj M) a s b n).symm).trans
        ((AffineModulePullbackSections.sectionsIso
          (CommRingCat.ofHom (inclusion R S T)) M).hom.hom.map_smul _ _)

/-- Restrict the pulled-back coefficient scalars to the common base ring. -/
local instance pullbackCoefficientModule : Module R (moduleSpecΓFunctor.obj
    ((pullback (Spec.map (CommRingCat.ofHom (inclusion R S T)))).obj M)) :=
  Module.compHom _ (algebraMap R (S ⊗[R] T))

/-- The section comparison also preserves scalars from the common base. -/
theorem sections_rsmul (r : R) (x : S ⊗[R] moduleSpecΓFunctor.obj M) :
    sections R S T M (r • x) = r • sections R S T M x := by
  induction x using TensorProduct.inductionOn with
  | tmul s n =>
    have h := sections_smul_tmul R S T M (algebraMap R S r) s 1 n
    simpa only [one_smul, ← Algebra.smul_def, IsScalarTower.algebraMap_smul,
      ← smul_tmul', ← Algebra.TensorProduct.algebraMap_apply] using h
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- A base-linear version, suitable for tensoring by an additional affine factor. -/
def linearSections : S ⊗[R] moduleSpecΓFunctor.obj M ≃ₗ[R]
    moduleSpecΓFunctor.obj ((pullback (Spec.map (CommRingCat.ofHom (inclusion R S T)))).obj M) :=
  { sections R S T M with map_smul' := sections_rsmul R S T M }

end FLT.Mazur.AffinePairPullbackSections

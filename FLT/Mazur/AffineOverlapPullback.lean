/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModulePullbackSections
public import FLT.Mazur.AffineOverlapTensor
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual affine overlap pullbacks and their coefficients

The two projection sheaves have coefficients `N ⊗[R] S` and `S ⊗[R] N`.
The comparisons below retain both scalar actions. We also identify these
sheaves with pullbacks along the actual fiber-product projections, transported
across `pullbackSpecIso`.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
open scoped ChangeOfRings
universe u
namespace FLT.Mazur.AffineOverlapPullback
open AffineOverlapTensor AffineModulePullbackSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Coefficients of a sheaf on `Spec S`. -/
abbrev coefficients (M : (Spec (.of S)).Modules) := moduleSpecΓFunctor.obj M

variable (M : (Spec (.of S)).Modules) [M.IsQuasicoherent]

/-- Restrict coefficient scalars along the base algebra map. -/
local instance : Module R (coefficients S M) := Module.compHom _ (algebraMap R S)
/-- The restricted coefficient action agrees with the algebra tower. -/
local instance : IsScalarTower R S (coefficients S M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

/-- Sections of the actual first projection pullback in tensor coordinates. -/
def firstSections : coefficients S M ⊗[R] S ≃+
    moduleSpecΓFunctor.obj ((pullback (Spec.map (CommRingCat.ofHom (left R S)))).obj M) :=
  (firstExtension R S (coefficients S M)).symm.trans
    (sectionsIso (CommRingCat.ofHom (left R S)) M).toLinearEquiv.toAddEquiv

/-- Sections of the actual second projection pullback in tensor coordinates. -/
def secondSections : S ⊗[R] coefficients S M ≃+
    moduleSpecΓFunctor.obj ((pullback (Spec.map (CommRingCat.ofHom (right R S)))).obj M) :=
  (second R S (coefficients S M)).symm.trans
    (sectionsIso (CommRingCat.ofHom (right R S)) M).toLinearEquiv.toAddEquiv

/-- A first-projection pure tensor is the corresponding multiple of the pullback unit. -/
theorem firstSections_tmul (n : coefficients S M) (s : S) :
    firstSections R S M (n ⊗ₜ[R] s) =
      ((1 : S) ⊗ₜ[R] s) • (show moduleSpecΓFunctor.obj
        ((pullback (Spec.map (CommRingCat.ofHom (left R S)))).obj M) from
        ((pullbackPushforwardAdjunction (Spec.map (CommRingCat.ofHom (left R S)))).unit.app M).app
          ⊤ n) :=
  sectionsIso_tmul (CommRingCat.ofHom (left R S)) M _ n

/-- A second-projection pure tensor is the corresponding multiple of the pullback unit. -/
theorem secondSections_tmul (s : S) (n : coefficients S M) :
    secondSections R S M (s ⊗ₜ[R] n) =
      (s ⊗ₜ[R] (1 : S)) • (show moduleSpecΓFunctor.obj
        ((pullback (Spec.map (CommRingCat.ofHom (right R S)))).obj M) from
        ((pullbackPushforwardAdjunction (Spec.map (CommRingCat.ofHom (right R S)))).unit.app M).app
          ⊤ n) :=
  sectionsIso_tmul (CommRingCat.ofHom (right R S)) M _ n

/-- Both overlap scalars act correctly on the first projection coefficients. -/
theorem firstSections_smul_tmul (a b t : S) (n : coefficients S M) :
    firstSections R S M ((a • n) ⊗ₜ[R] (b * t)) =
      (a ⊗ₜ[R] b) • firstSections R S M (n ⊗ₜ[R] t) := by
  change (sectionsIso (CommRingCat.ofHom (left R S)) M).hom _ =
    (a ⊗ₜ[R] b) • (sectionsIso (CommRingCat.ofHom (left R S)) M).hom _
  exact (congrArg (sectionsIso (CommRingCat.ofHom (left R S)) M).hom
    (firstExtension_symm_smul_tmul R S (coefficients S M) a b t n).symm).trans
      ((sectionsIso (CommRingCat.ofHom (left R S)) M).hom.hom.map_smul _ _)

/-- Both overlap scalars act correctly on the second projection coefficients. -/
theorem secondSections_smul_tmul (a b t : S) (n : coefficients S M) :
    secondSections R S M ((a * t) ⊗ₜ[R] (b • n)) =
      (a ⊗ₜ[R] b) • secondSections R S M (t ⊗ₜ[R] n) := by
  change (sectionsIso (CommRingCat.ofHom (right R S)) M).hom _ =
    (a ⊗ₜ[R] b) • (sectionsIso (CommRingCat.ofHom (right R S)) M).hom _
  exact (congrArg (sectionsIso (CommRingCat.ofHom (right R S)) M).hom
    (second_symm_smul_tmul R S (coefficients S M) a b t n).symm).trans
      ((sectionsIso (CommRingCat.ofHom (right R S)) M).hom.hom.map_smul _ _)

/-- The first comparison is linear for the first copy of `S`. -/
theorem firstSections_smul (a : S) (x : coefficients S M ⊗[R] S) :
    firstSections R S M (a • x) =
      (a ⊗ₜ[R] (1 : S)) • firstSections R S M x := by
  induction x using TensorProduct.inductionOn with
  | tmul n t =>
    simpa only [smul_tmul', one_mul] using firstSections_smul_tmul R S M a 1 t n
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- The second comparison is linear for the first copy of `S`. -/
theorem secondSections_smul (a : S) (x : S ⊗[R] coefficients S M) :
    secondSections R S M (a • x) =
      (a ⊗ₜ[R] (1 : S)) • secondSections R S M x := by
  induction x using TensorProduct.inductionOn with
  | tmul t n =>
    simpa only [smul_tmul', smul_eq_mul, one_smul] using
      secondSections_smul_tmul R S M a 1 t n
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- The second copy of `S` acts on the coefficient factor of the second tensor module. -/
theorem secondSections_other_smul (a : S) (x : S ⊗[R] coefficients S M) :
    secondSections R S M ((Algebra.lsmul R R (coefficients S M) a).lTensor S x) =
      ((1 : S) ⊗ₜ[R] a) • secondSections R S M x := by
  induction x using TensorProduct.inductionOn with
  | tmul t n =>
    simpa only [LinearMap.lTensor_tmul, Algebra.lsmul_coe, one_mul] using
      secondSections_smul_tmul R S M 1 a t n
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

/-- Transport the first fiber-product projection sheaf to the tensor spectrum. -/
def firstProjectionIso :
    (pullback (pullbackSpecIso R S S).inv).obj
      ((pullback (Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))))).obj M) ≅
      (pullback (Spec.map (CommRingCat.ofHom (left R S)))).obj M :=
  (pullbackComp _ _).app M ≪≫ (pullbackCongr (pullbackSpecIso_inv_fst R S S)).app M

/-- Transport the second fiber-product projection sheaf to the tensor spectrum. -/
def secondProjectionIso :
    (pullback (pullbackSpecIso R S S).inv).obj
      ((pullback (Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))))).obj M) ≅
      (pullback (Spec.map (CommRingCat.ofHom (right R S)))).obj M :=
  (pullbackComp _ _).app M ≪≫ (pullbackCongr (pullbackSpecIso_inv_snd R S S)).app M

end FLT.Mazur.AffineOverlapPullback

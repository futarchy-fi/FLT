/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentReverseCover
public import FLT.Mazur.WeierstrassDividedSecantSource

/-!
# Actual reversed slope maps from the two tangent-cover members

Each map is a localization lift, retaining the full map from the common
input ring. The secant member reverses both signs; the tangent member
inverts precisely the reversed tangent denominator.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "C" b => Localization.Away (dividedTangentReverseCoverElement W s b3 b4 b6 a c b)
local notation "j" b => (IsScalarTower.toAlgHom R T (C b)).comp (IsScalarTower.toAlgHom R S T)
local notation "V" => DividedSecantRing W s b3 b4 b6 c a
local notation "U" => DividedTangentRing W s b3 b4 b6 c a

/-- The reversed secant denominator is invertible on the first cover member. -/
theorem dividedTangentReverseCover_secantUnit :
    IsUnit ((j false) (c (x W s b3 b4 b6) - a (x W s b3 b4 b6))) := by
  have h := (IsLocalization.Away.algebraMap_isUnit (S := C false)
    (dividedTangentReverseCoverElement W s b3 b4 b6 a c false)).neg
  change IsUnit (-(algebraMap T (C false)
    (algebraMap S T (a (x W s b3 b4 b6) - c (x W s b3 b4 b6))))) at h
  simpa only [map_sub, neg_sub, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] using h

/-- The actual reversed secant lift from the first principal open. -/
def dividedTangentReverseCoverSecant : V →ₐ[R] C false :=
  IsLocalization.Away.liftAlgHom _ (f := j false)
    (dividedTangentReverseCover_secantUnit W s b3 b4 b6 a c)

/-- The actual reversed tangent lift from the second principal open. -/
def dividedTangentReverseCoverTangent : U →ₐ[R] C true :=
  IsLocalization.Away.liftAlgHom (dividedTangentDenominator W s b3 b4 b6 c a)
    (f := j true) (by
      change IsUnit (algebraMap T (C true)
        (dividedTangentReverseCoverElement W s b3 b4 b6 a c true))
      exact IsLocalization.Away.algebraMap_isUnit (S := C true) _)

/-- The secant lift keeps the entire original input algebra map. -/
theorem dividedTangentReverseCoverSecant_base (z : S) :
    dividedTangentReverseCoverSecant W s b3 b4 b6 a c (algebraMap S V z) = (j false) z := by
  simp only [dividedTangentReverseCoverSecant, IsLocalization.Away.coe_liftAlgHom,
    IsLocalization.Away.lift_eq]
  rfl

/-- The tangent lift keeps the same complete input algebra map. -/
theorem dividedTangentReverseCoverTangent_base (z : S) :
    dividedTangentReverseCoverTangent W s b3 b4 b6 a c (algebraMap S U z) = (j true) z := by
  simp only [dividedTangentReverseCoverTangent, IsLocalization.Away.coe_liftAlgHom,
    IsLocalization.Away.lift_eq]
  rfl

/-- The secant spectrum map lies over the original pair base. -/
@[reassoc] theorem dividedTangentReverseCoverSecant_spec :
    Spec.map (CommRingCat.ofHom (dividedTangentReverseCoverSecant W s b3 b4 b6 a c).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S V)) =
      (dividedTangentReverseCover W s b3 b4 b6 a c).f false ≫
        Spec.map (CommRingCat.ofHom (algebraMap S T)) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext z
  exact dividedTangentReverseCoverSecant_base W s b3 b4 b6 a c z

/-- The tangent spectrum map lies over the same original pair base. -/
@[reassoc] theorem dividedTangentReverseCoverTangent_spec :
    Spec.map (CommRingCat.ofHom (dividedTangentReverseCoverTangent W s b3 b4 b6 a c).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S U)) =
      (dividedTangentReverseCover W s b3 b4 b6 a c).f true ≫
        Spec.map (CommRingCat.ofHom (algebraMap S T)) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext z
  exact dividedTangentReverseCoverTangent_base W s b3 b4 b6 a c z

end FLT.Mazur.WeierstrassDilatation

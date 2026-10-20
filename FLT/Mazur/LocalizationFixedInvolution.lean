/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Extending a fixed-coordinate involution to its actual principal open

An algebra involution fixing the denominator extends uniquely to localization.
This constructs the boundary automorphisms used in successive chart gluing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.LocalizationFixedInvolution
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (f : A →ₐ[R] A) (a : A) (ha : f a = a)
local notation "L" => Localization.Away a

/-- Extend the actual algebra map across its fixed denominator. -/
def lift : L →ₐ[R] L :=
  IsLocalization.Away.liftAlgHom a
    (f := (IsScalarTower.toAlgHom R A L).comp f) (by
      change IsUnit (algebraMap A L (f a))
      rw [ha]
      exact IsLocalization.Away.algebraMap_isUnit a)

/-- The extension retains every original regular function. -/
@[simp] theorem lift_base (z : A) :
    lift f a ha (algebraMap A L z) = algebraMap A L (f z) := by
  rw [lift, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- An involution remains involutive after localization at its fixed coordinate. -/
theorem lift_comp (hf : f.comp f = AlgHom.id R A) :
    (lift f a ha).comp (lift f a ha) = AlgHom.id R L := by
  apply IsLocalization.algHom_ext (Submonoid.powers a)
  ext z
  change lift f a ha (lift f a ha (algebraMap A L z)) = algebraMap A L z
  rw [lift_base, lift_base]
  exact congrArg (algebraMap A L) (AlgHom.congr_fun hf z)

/-- The localization carries the constructed algebra automorphism. -/
def equiv (hf : f.comp f = AlgHom.id R A) : L ≃ₐ[R] L :=
  AlgEquiv.ofAlgHom (lift f a ha) (lift f a ha)
    (lift_comp f a ha hf) (lift_comp f a ha hf)

/-- The full principal-open scheme has the constructed involution. -/
def specIso (hf : f.comp f = AlgHom.id R A) : Spec (.of L) ≅ Spec (.of L) :=
  Scheme.Spec.mapIso (equiv f a ha hf).toRingEquiv.toCommRingCatIso.op

/-- The localization involution preserves the actual principal-open inclusion. -/
@[reassoc] theorem specIso_inclusion (hf : f.comp f = AlgHom.id R A) :
    (specIso f a ha hf).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A L)) =
      Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫
        Spec.map (CommRingCat.ofHom f.toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  congr 1
  ext z
  exact lift_base f a ha z

end FLT.Mazur.LocalizationFixedInvolution

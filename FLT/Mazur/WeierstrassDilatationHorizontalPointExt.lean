/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationHorizontalCongruence
public import FLT.Mazur.PrincipalOpenTensor

/-!
# Original coordinates determine horizontal tensor points

Localization introduces no extra freedom for point evaluations. After tensor
base change, equality of actual spectrum maps is exactly equality of the two
original divided coordinate values.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
local notation "C" => Coordinate W s b3 b4 b6
local notation "B" => HorizontalCoordinate W s b3 b4 b6
local notation "x" => WeierstrassDilatation.x W s b3 b4 b6
local notation "y" => WeierstrassDilatation.y W s b3 b4 b6

/-- Two original coordinate values determine every horizontal localized function. -/
theorem horizontalPoint_eq_iff (f g : B →ₐ[R] S) :
    f = g ↔ f (algebraMap C B x) = g (algebraMap C B x) ∧
      f (algebraMap C B y) = g (algebraMap C B y) := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hx, hy⟩
    apply IsLocalization.algHom_ext (Submonoid.powers x)
    apply WeierstrassDilatation.hom_ext
    · exact hx
    · exact hy

/-- The actual horizontal tensor spectrum map remembers precisely those coordinate values. -/
theorem horizontalTensorPoint_eq_iff (f g : B →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom (AlgHom.liftEquiv R S B S f).toRingHom) =
      Spec.map (CommRingCat.ofHom (AlgHom.liftEquiv R S B S g).toRingHom) ↔
        f (algebraMap C B x) = g (algebraMap C B x) ∧
          f (algebraMap C B y) = g (algebraMap C B y) := by
  rw [← horizontalPoint_eq_iff]
  constructor
  · intro he
    apply (AlgHom.liftEquiv R S B S).injective
    exact AlgHom.coe_ringHom_injective
      (congrArg CommRingCat.Hom.hom (Spec.map_injective he))
  · rintro rfl
    rfl

end FLT.Mazur.WeierstrassDilatation

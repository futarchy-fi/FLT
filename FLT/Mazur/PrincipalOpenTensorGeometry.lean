/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenTensorTransition
public import FLT.Mazur.TensorOpenChart

/-!
# Restriction and transition squares for tensor principal opens

Both squares retain all original functions. These identities allow an
integral atlas overlap to be transported into the actual coefficient pullback.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.PrincipalOpenTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (x : A) (y : B) (e : Localization.Away x ≃ₐ[R] Localization.Away y)

/-- The actual principal-open inclusion in the tensor spectrum. -/
def inclusion : Spec (.of (Localization.Away ((1 : S) ⊗ₜ[R] x))) ⟶
    Spec (.of (S ⊗[R] A)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (S ⊗[R] A) _))

instance inclusion_isOpenImmersion : IsOpenImmersion (inclusion (R := R) S x) :=
  IsOpenImmersion.of_isLocalization ((1 : S) ⊗ₜ[R] x)

/-- The tensor principal open projects to its original integral principal open. -/
def projection : Spec (.of (Localization.Away ((1 : S) ⊗ₜ[R] x))) ⟶
    Spec (.of (Localization.Away x)) :=
  Spec.map (CommRingCat.ofHom (coefficient (R := R) S x).toRingHom)

/-- Restriction commutes with projection on every original function. -/
@[reassoc] theorem inclusion_projection :
    inclusion (R := R) S x ≫ TensorOpenChart.projection =
      projection (R := R) S x ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x))) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext fun a => (coefficient_base S x a).symm

/-- The transition of actual tensor localizations as a scheme isomorphism. -/
def transitionIso : Spec (.of (Localization.Away ((1 : S) ⊗ₜ[R] y))) ≅
    Spec (.of (Localization.Away ((1 : S) ⊗ₜ[R] x))) :=
  Scheme.Spec.mapIso (transition (R := R) S x y e).toRingEquiv.toCommRingCatIso.op

/-- The entire original integral overlap map survives coefficient extension. -/
@[reassoc] theorem transitionIso_projection :
    (transitionIso (R := R) S x y e).hom ≫ projection (R := R) S x =
      projection (R := R) S y ≫ Spec.map (CommRingCat.ofHom e.toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (transition_coefficient (R := R) S x y e)

/-- Restricting the tensor chart preserves its coefficient structure. -/
@[reassoc] theorem inclusion_structure :
    inclusion (R := R) S x ≫ Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))) =
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away ((1 : S) ⊗ₜ[R] x)))) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1


/-- The overlap transition retains the extended coefficient structure. -/
@[reassoc] theorem transitionIso_structure :
    (transitionIso (R := R) S x y e).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away ((1 : S) ⊗ₜ[R] x)))) =
        Spec.map (CommRingCat.ofHom (algebraMap S
          (Localization.Away ((1 : S) ⊗ₜ[R] y)))) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (transition (R := R) S x y e).commutes

end FLT.Mazur.PrincipalOpenTensor

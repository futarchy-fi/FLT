/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSpecSections

/-!
# Recovering chart morphisms from global sections

The unit of the Gamma-Spec adjunction turns any global-section ring map back
into a morphism. The two explicit constructions are inverse and preserve
composition, so algebra localization lifts apply to arbitrary source schemes.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {X : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B]

/-- The scheme morphism represented by a ring map into global sections. -/
def specSectionMorphism (f : A →+* Γ(X, ⊤)) : X ⟶ Spec (.of A) :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)

/-- Recovering a morphism preserves the original map of global sections. -/
theorem specSectionHom_morphism (f : A →+* Γ(X, ⊤)) :
    specSectionHom (specSectionMorphism f) = f := by
  rw [specSectionMorphism, specSectionHom_comp]
  have h : specSectionHom X.toSpecΓ = RingHom.id _ := by
    unfold specSectionHom
    rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id]
    rfl
  rw [h, RingHom.id_comp]

/-- Recovering the global sections of a chart morphism gives that same morphism. -/
theorem specSectionMorphism_hom (f : X ⟶ Spec (.of A)) :
    specSectionMorphism (specSectionHom f) = f := by
  apply specSectionHom_injective
  exact specSectionHom_morphism _

/-- Ring-map composition gives chart composition after recovery. -/
theorem specSectionMorphism_comp (f : A →+* Γ(X, ⊤)) (g : B →+* A) :
    specSectionMorphism (f.comp g) =
      specSectionMorphism f ≫ Spec.map (CommRingCat.ofHom g) := by
  apply specSectionHom_injective
  rw [specSectionHom_comp, specSectionHom_morphism, specSectionHom_morphism]

end FLT.Mazur.WeierstrassIntegralChart

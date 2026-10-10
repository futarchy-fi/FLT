/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupAffineQuotient
public import Mathlib.CategoryTheory.Endomorphism

/-!
# The genuine scheme action associated to a ring action

The inverse ring action gives a monoid homomorphism into scheme automorphisms.
The fixed-ring quotient is invariant under this actual scheme action.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteGroupQuotient

universe u
variable (G A : Type u) [Group G] [CommRing A] [MulSemiringAction G A]

/-- The identity ring action induces the identity scheme morphism. -/
lemma actionMap_one : actionMap G A 1 = 𝟙 _ := by
  unfold actionMap
  have h : CommRingCat.ofHom (MulSemiringAction.toRingHom G A 1) = 𝟙 (CommRingCat.of A) := by
    ext a
    exact one_smul G a
  rw [h, Spec.map_id]

/-- Ring-action multiplication becomes scheme-morphism composition in this order. -/
lemma actionMap_mul (g h : G) : actionMap G A (g * h) = actionMap G A g ≫ actionMap G A h := by
  rw [actionMap, actionMap, actionMap, ← Spec.map_comp]
  apply congrArg Spec.map
  ext a
  exact mul_smul g h a

/-- Pullback by the inverse group element defines the actual scheme automorphism. -/
def spectrumAut (g : G) : Aut (Spec (.of A)) where
  hom := actionMap G A g⁻¹
  inv := actionMap G A g
  hom_inv_id := by rw [← actionMap_mul, inv_mul_cancel, actionMap_one]
  inv_hom_id := by rw [← actionMap_mul, mul_inv_cancel, actionMap_one]

/-- The genuine group action on the spectrum of the ring. -/
def spectrumAction : G →* Aut (Spec (.of A)) where
  toFun := spectrumAut G A
  map_one' := by
    apply Aut.ext
    change actionMap G A (1 : G)⁻¹ = 𝟙 _
    rw [inv_one, actionMap_one]
  map_mul' g h := by
    apply Aut.ext
    change actionMap G A (g * h)⁻¹ = actionMap G A h⁻¹ ≫ actionMap G A g⁻¹
    rw [mul_inv_rev, actionMap_mul]

/-- The actual scheme automorphism computes by the inverse coordinate action. -/
lemma spectrumAction_hom (g : G) : (spectrumAction G A g).hom = actionMap G A g⁻¹ := rfl

/-- The fixed-ring quotient is invariant under the genuine group action. -/
@[reassoc]
lemma spectrumAction_quotientMap (g : G) :
    (spectrumAction G A g).hom ≫ quotientMap G A = quotientMap G A :=
  actionMap_quotientMap G A g⁻¹

/-- Invariance under all coordinate actions equals invariance under the actual scheme action. -/
lemma spectrumAction_invariant_iff {Y : Scheme.{u}} (f : Spec (.of A) ⟶ Y) :
    (∀ g, (spectrumAction G A g).hom ≫ f = f) ↔ ∀ g, actionMap G A g ≫ f = f := by
  constructor
  · intro h g
    simpa only [spectrumAction_hom, inv_inv] using h g⁻¹
  · intro h g
    exact h g⁻¹

end FLT.Mazur.FiniteGroupQuotient

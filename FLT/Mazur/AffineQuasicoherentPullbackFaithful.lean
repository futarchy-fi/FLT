/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFaithfullyFlatPullbackFaithful

/-!
# Faithfully flat pullback detects maps of affine quasi-coherent sheaves

Conjugating by the affine tilde counits extends faithfulness from tilde
objects to arbitrary quasi-coherent sheaves, including affine refinements.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineQuasicoherentPullbackFaithful
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.FaithfullyFlat)
variable {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]

include hφ

/-- Faithfully flat pullback detects maps between arbitrary quasi-coherent sheaves. -/
theorem map_injective (f g : M ⟶ N)
    (h : (pullback (Spec.map φ)).map f = (pullback (Spec.map φ)).map g) : f = g := by
  apply (cancel_epi M.fromTildeΓ).mp
  apply (cancel_mono (inv N.fromTildeΓ)).mp
  apply AffineFaithfullyFlatPullbackFaithful.tilde_map_injective φ hφ
  simp only [Functor.map_comp, h]

/-- Equality can be checked after faithfully flat pullback. -/
theorem map_eq_iff (f g : M ⟶ N) :
    (pullback (Spec.map φ)).map f = (pullback (Spec.map φ)).map g ↔ f = g :=
  ⟨map_injective φ hφ f g, fun h ↦ congrArg (pullback (Spec.map φ)).map h⟩

/-- A reconstruction square uniquely determines an arbitrary quasi-coherent map. -/
theorem reconstruction_unique {P : (Spec S).Modules}
    (e : (pullback (Spec.map φ)).obj N ≅ P) (f g : M ⟶ N)
    (h : (pullback (Spec.map φ)).map f ≫ e.hom =
      (pullback (Spec.map φ)).map g ≫ e.hom) : f = g :=
  map_injective φ hφ f g ((cancel_mono e.hom).mp h)

/-- A proposed inverse can be checked after faithfully flat pullback. -/
theorem inverse_of_pullback (f : M ⟶ N) (g : N ⟶ M)
    (hfg : (pullback (Spec.map φ)).map f ≫ (pullback (Spec.map φ)).map g = 𝟙 _)
    (hgf : (pullback (Spec.map φ)).map g ≫ (pullback (Spec.map φ)).map f = 𝟙 _) :
    f ≫ g = 𝟙 M ∧ g ≫ f = 𝟙 N := by
  constructor
  · apply map_injective φ hφ
    erw [Functor.map_comp, CategoryTheory.Functor.map_id]
    exact hfg
  · apply map_injective φ hφ
    erw [Functor.map_comp, CategoryTheory.Functor.map_id]
    exact hgf

end FLT.Mazur.AffineQuasicoherentPullbackFaithful

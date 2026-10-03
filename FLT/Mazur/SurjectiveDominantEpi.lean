/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
/-!
# Epimorphisms from surjective schematic dominance

Injectivity on sections and surjectivity on points give cancellation against
arbitrary targets. Injective ring maps supply the affine dominance hypothesis.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace FLT.Mazur.SurjectiveDominantEpi
variable {X Y : Scheme.{u}}
/-- Surjectivity and injective section maps imply categorical cancellation. -/
theorem epi (f : X ⟶ Y) [Surjective f] [QuasiCompact f]
    [IsSchemeTheoreticallyDominant f] : Epi f := by
  constructor
  intro Z g h e
  have hb : g.base = h.base := ConcreteCategory.hom_ext _ _ fun y ↦ by
    obtain ⟨x, rfl⟩ := (show Function.Surjective f from Surjective.surj) y
    exact congrArg (fun m : X ⟶ Z ↦ m x) e
  apply Scheme.Hom.ext hb
  intro U
  have hm : Mono (f.app (h ⁻¹ᵁ U)) := ConcreteCategory.mono_of_injective _ (f.app_injective _)
  apply (cancel_mono (f.app (h ⁻¹ᵁ U))).mp
  rw [Category.assoc, f.naturality]
  have ee := Scheme.Hom.congr_app e U
  rw [← Category.assoc, ← Scheme.Hom.comp_app, ee]
  simp only [Category.assoc, eqToHom_map, eqToHom_op, eqToHom_unop, eqToHom_trans,
    eqToHom_refl, Category.comp_id, Scheme.Hom.comp_app]
variable {C D : Type u} [CommRing C] [CommRing D]
/-- An injective ring map induces a scheme-theoretically dominant morphism. -/
theorem spec_schematic (f : C →+* D) (hf : Function.Injective f) :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom f)) := by
  rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine]
  have ha : Function.Injective (Spec.map (CommRingCat.ofHom f)).appTop := by
    have hi : Mono (CommRingCat.ofHom f) := ConcreteCategory.mono_of_injective _ hf
    have hi' : Mono (Spec.map (CommRingCat.ofHom f)).appTop :=
      (MorphismProperty.monomorphisms _).arrow_mk_iso_iff
        (arrowIsoΓSpecOfIsAffine (CommRingCat.ofHom f)) |>.mp hi
    exact (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp hi'
  rw [(RingHom.injective_iff_ker_eq_bot _).mp ha]
  apply Scheme.IdealSheafData.ext
  funext U
  simp
end FLT.Mazur.SurjectiveDominantEpi

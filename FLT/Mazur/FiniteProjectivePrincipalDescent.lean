/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Finite projective modules descend from indexed principal covers

The local modules and localization maps may be arbitrary models. The unit-ideal
condition permits descent of finite presentation and flatness, hence projectivity.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PrincipalSubmodulePatching
variable {A V ι : Type*} [CommRing A] [AddCommGroup V] [Module A V]
  (r : ι → A) (hr : Ideal.span (Set.range r) = ⊤)
  (B : ι → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
  [∀ i, IsLocalization.Away (r i) (B i)]
  (W : ι → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module A (W i)]
  [∀ i, Module (B i) (W i)] [∀ i, IsScalarTower A (B i) (W i)]
  (g : ∀ i, V →ₗ[A] W i) [∀ i, IsLocalizedModule (.powers (r i)) (g i)]

include hr g in
/-- Finite projectivity descends from any indexed unit-ideal principal cover. -/
theorem finiteProjective_of_principal_cover
    (hfin : ∀ i, Module.Finite (B i) (W i))
    (hproj : ∀ i, Module.Projective (B i) (W i)) :
    Module.FinitePresentation A V ∧ Module.Projective A V := by
  let s := Set.range r
  let j : s → ι := fun a ↦ a.property.choose
  have hj (a : s) : r (j a) = a.val := a.property.choose_spec
  let _ (a : s) : IsLocalization.Away a.val (B (j a)) := by
    rw [← hj a]
    infer_instance
  let _ (a : s) : IsLocalizedModule (.powers a.val) (g (j a)) := by
    rw [← hj a]
    infer_instance
  let _ (i : ι) : Module.Finite (B i) (W i) := hfin i
  let _ (i : ι) : Module.Projective (B i) (W i) := hproj i
  have hfp : Module.FinitePresentation A V :=
    Module.FinitePresentation.of_localizationSpan' s hr
      (Rₚ := fun a ↦ B (j a)) (fun a ↦ g (j a))
      (fun a ↦ Module.finitePresentation_of_projective (B (j a)) (W (j a)))
  let _ := hfp
  have hflat : Module.Flat A V := by
    apply Module.flat_of_isLocalized_span A V s hr (fun a ↦ W (j a))
      (fun a ↦ g (j a))
    intro a
    exact (Module.flat_iff_of_isLocalization (B (j a)) (.powers (r (j a)))
      (W (j a))).mp inferInstance
  let _ := hflat
  exact ⟨hfp, Module.Flat.projective_of_finitePresentation⟩

end FLT.Mazur.PrincipalSubmodulePatching

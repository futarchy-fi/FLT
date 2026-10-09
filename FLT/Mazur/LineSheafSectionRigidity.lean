/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSheafGlobalEndomorphisms
public import FLT.Mazur.ScalarEndomorphismPullback
public import FLT.Mazur.ModuleLineBundlePullback

/-!
# Detecting line endomorphisms at a section

When every global function comes from the base, restriction along a section
is faithful on line endomorphisms. A chosen rigidification then kills automorphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve.LineSheafSectionRigidity
open ModuleSheafScalarEndomorphisms IdealPowerScalarLift
variable {X S : Scheme.{u}} (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
  (hf : Function.Surjective f.appTop)

include hs hf in
/-- Section evaluation detects functions if all functions descend from the base. -/
lemma section_appTop_injective : Function.Injective s.appTop := by
  have split (a : Γ(S, ⊤)) : s.appTop (f.appTop a) = a := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hs, Scheme.Hom.id_appTop]
    rfl
  intro a b hab
  obtain ⟨r, rfl⟩ := hf a
  obtain ⟨t, rfl⟩ := hf b
  rw [split, split] at hab
  rw [hab]

include hs hf in
/-- Actual restriction to the section detects equality of all line endomorphisms. -/
theorem pullback_end_injective {M : X.Modules} (hM : LocallyFreeRankOne M) :
    Function.Injective (fun φ : M ⟶ M ↦ (pullback s).map φ) := by
  intro φ ψ h
  obtain ⟨r, rfl⟩ := (scalarEnd_bijective hM).surjective φ
  obtain ⟨t, rfl⟩ := (scalarEnd_bijective hM).surjective ψ
  congr 1
  apply section_appTop_injective f s hs hf
  apply (scalarEnd_bijective (hM.pullback s)).injective
  simpa only [scalarEnd_pullback] using h

include hs hf in
/-- An endomorphism restricting to the identity is the identity. -/
theorem end_eq_id {M : X.Modules} (hM : LocallyFreeRankOne M) (φ : M ⟶ M)
    (hφ : (pullback s).map φ = 𝟙 _) : φ = 𝟙 M := by
  apply pullback_end_injective f s hs hf hM
  exact hφ.trans ((pullback s).map_id M).symm

include hs hf in
/-- An automorphism preserving an actual rigidification is trivial. -/
theorem rigidified_auto_eq_refl {M : X.Modules} (hM : LocallyFreeRankOne M)
    (ρ : (pullback s).obj M ≅ structureModule S) (e : M ≅ M)
    (he : (pullback s).map e.hom ≫ ρ.hom = ρ.hom) : e = Iso.refl M := by
  apply Iso.ext
  apply end_eq_id f s hs hf hM
  apply (cancel_mono ρ.hom).mp
  simpa only [Category.id_comp] using he

end FLT.Mazur.FCurve.LineSheafSectionRigidity

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafMorphismGluing

/-!
# Gluing two actual module-sheaf sections

Sections on a two-open cover glue uniquely when they agree on the full
intersection. An affine representative of that intersection may be used.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.ModuleSheafBinarySections

universe u
variable {X : Scheme.{u}} (M : X.Modules)

/-- Ordinary restriction of an actual module-sheaf section. -/
abbrev res {U V : X.Opens} (h : V ≤ U) (s : Γ(M, U)) : Γ(M, V) :=
  M.presheaf.map (homOfLE h).op s

/-- Restriction through an intermediate open gives the same section. -/
theorem res_res {U V T : X.Opens} (h : V ≤ U) (k : T ≤ V) (s : Γ(M, U)) :
    res M k (res M h s) = res M (k.trans h) s := by
  change (M.presheaf.map (homOfLE h).op ≫ M.presheaf.map (homOfLE k).op) s = _
  rw [← M.presheaf.map_comp]
  rfl

/-- The sheaf gluing property on a binary cover, with a specified full intersection. -/
theorem existsUnique_glue {U V T : X.Opens} (hcover : U ⊔ V = ⊤)
    (hT : T = U ⊓ V) (hTU : T ≤ U) (hTV : T ≤ V)
    (s : Γ(M, U)) (t : Γ(M, V)) (h : res M hTU s = res M hTV t) :
    ∃! z : Γ(M, ⊤), res M le_top z = s ∧ res M le_top z = t := by
  subst T
  let C : Bool → X.Opens := fun b ↦ if b then U else V
  let c : ∀ b, Γ(M, C b) := fun b ↦ by cases b <;> [exact t; exact s]
  have hc : TopCat.Presheaf.IsCompatible M.presheaf C c := by
    intro i j
    cases i <;> cases j
    · rfl
    · change res M inf_le_left t = res M inf_le_right s
      have he : V ⊓ U = U ⊓ V := inf_comm _ _
      have hr := congrArg (fun z ↦ M.presheaf.map (eqToHom he).op z) h.symm
      simp only [res, ← ConcreteCategory.comp_apply, ← Functor.map_comp] at hr
      have hl : (homOfLE hTV).op ≫ (eqToHom he).op =
          (homOfLE (show V ⊓ U ≤ V from inf_le_left)).op := Subsingleton.elim _ _
      have hr' : (homOfLE hTU).op ≫ (eqToHom he).op =
          (homOfLE (show V ⊓ U ≤ U from inf_le_right)).op := Subsingleton.elim _ _
      rw [hl, hr'] at hr
      exact hr
    · exact h
    · rfl
  have hcov : (⊤ : X.Opens) ≤ ⨆ b, C b := by
    rw [← hcover, sup_le_iff]
    exact ⟨le_iSup C true, le_iSup C false⟩
  obtain ⟨z, hz, hu⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X) C ⊤ (fun _ ↦ homOfLE le_top) hcov c hc
  refine ⟨z, ⟨hz true, hz false⟩, ?_⟩
  intro w hw
  apply hu w
  intro b
  cases b
  · exact hw.2
  · exact hw.1

end FLT.Mazur.ModuleSheafBinarySections

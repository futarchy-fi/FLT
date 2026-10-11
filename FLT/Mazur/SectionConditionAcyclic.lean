/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealQuotientSectionLift

/-!
# Preserving acyclicity when imposing a section condition

For an acyclic middle term, the kernel stays acyclic exactly when all global
quotient sections lift. This uses the actual connecting map, and applies to
point conditions without replacing the ideal by its support.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))
  (S : ShortComplex X.Modules) (hS : S.ShortExact)

/-- Surjectivity of global quotient sections also gives surjectivity on H⁰. -/
theorem moduleScalarHMap_zero_surjective_of_sections
    (hg : Function.Surjective (S.g.app ⊤)) :
    Function.Surjective (moduleScalarHMap f S.g 0) := by
  intro t
  obtain ⟨s, hs⟩ := hg (moduleScalarH0Equiv f S.X₃ t)
  refine ⟨(moduleScalarH0Equiv f S.X₂).symm s, ?_⟩
  apply (moduleScalarH0Equiv f S.X₃).injective
  rw [moduleScalarH0Equiv_naturality, LinearEquiv.apply_symm_apply, hs]

include hS in
/-- A surjective section condition preserves H¹ vanishing in its actual kernel. -/
theorem kernel_h1_vanishing_of_sections_surjective
    [Subsingleton (ModuleScalarH f S.X₂ 1)]
    (hg : Function.Surjective (S.g.app ⊤)) :
    Subsingleton (ModuleScalarH f S.X₁ 1) := by
  let hAb := CoherentDevissage.moduleToSheaf_shortExact hS
  have hsur := moduleScalarHMap_zero_surjective_of_sections f S hg
  have hz (x : ModuleScalarH f S.X₁ 1) : x = 0 := by
    obtain ⟨y, hy⟩ := (moduleScalarH_exact₁ S hAb f 0 x).mp (Subsingleton.elim _ _)
    obtain ⟨z, rfl⟩ := hsur y
    have he := (moduleScalarH_exact₃ S hAb f 0
      (moduleScalarHMap f S.g 0 z)).mpr ⟨z, rfl⟩
    exact hy.symm.trans he
  exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩

include hS in
/-- For an acyclic middle term, no other obstruction to the condition exists. -/
theorem kernel_h1_vanishing_iff_sections_surjective
    [Subsingleton (ModuleScalarH f S.X₂ 1)] :
    Subsingleton (ModuleScalarH f S.X₁ 1) ↔ Function.Surjective (S.g.app ⊤) := by
  constructor
  · intro hz
    let _ : Subsingleton (ModuleH S.X₁ 1) := hz
    exact globalSections_surjective_of_kernel_h1 S hS
  · exact kernel_h1_vanishing_of_sections_surjective f S hS

end FLT.Mazur.FCurve

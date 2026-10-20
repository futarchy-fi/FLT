/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Equality of sections from open neighborhood pullbacks

Equality on one open neighborhood of every point implies exact equality
in the original structure sheaf, including all nilpotent sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeLocalSectionEquality
universe u
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme.{u}}

/-- Pullbacks to open neighborhoods jointly detect global sections. -/
theorem eq_of_locally_eq (s t : Γ(X, ⊤))
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ U.ι.appTop s = U.ι.appTop t) :
    s = t := by
  apply TopCat.Presheaf.section_ext X.sheaf
  intro x hx
  change X.presheaf.germ ⊤ x hx s = X.presheaf.germ ⊤ x hx t
  obtain ⟨U, hxU, he⟩ := h x
  have hx' : x ∈ U.ι ''ᵁ ⊤ := ⟨⟨x, hxU⟩, trivial, rfl⟩
  have hg := congrArg (X.presheaf.germ (U.ι ''ᵁ ⊤) x hx') he
  change X.presheaf.germ (U.ι ''ᵁ ⊤) x hx'
      (X.presheaf.map (homOfLE le_top).op s) =
    X.presheaf.germ (U.ι ''ᵁ ⊤) x hx'
      (X.presheaf.map (homOfLE le_top).op t) at hg
  simpa only [TopCat.Presheaf.germ_res_apply] using hg

end FLT.Mazur.SchemeLocalSectionEquality

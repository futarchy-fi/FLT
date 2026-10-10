/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionExactness

/-!
# Transport of actual section maps through an isomorphism

Prove the transport once for arbitrary module sheaves, keeping concrete
large quotient and tensor-line comparisons opaque at their applications.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} {M N P : X.Modules}

/-- Surjective global sections remain surjective under an actual target isomorphism. -/
theorem moduleSections_surjective_of_comp_iso (p : M ⟶ N) (e : N ≅ P) (g : M ⟶ P)
    (he : p ≫ e.hom = g) (hp : Function.Surjective (p.app ⊤)) :
    Function.Surjective (g.app ⊤) := by
  intro s
  obtain ⟨t, ht⟩ := hp (e.inv.app ⊤ s)
  refine ⟨t, ?_⟩
  rw [← he]
  change e.hom.app ⊤ (p.app ⊤ t) = s
  rw [ht]
  exact congr($(e.inv_hom_id).app ⊤ s)

end FLT.Mazur.FCurve

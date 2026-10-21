/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemeOpenChartRange

/-!
# Image tests through boundary chart isomorphisms

Source reindexing preserves images and target reindexing transports membership.
These lemmas separate geometric range arguments from large coordinate algebras.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
/-- Reindexing the target of an open chart transports its exact membership test. -/
theorem arithmeticBoundary_range_targetIso {A B C : Scheme} (e : A ≅ B)
    (f : C ⟶ A) (p : B) : p ∈ Set.range (f ≫ e.hom) ↔ e.inv p ∈ Set.range f := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, ((Scheme.homeoOfIso e).left_inv (f z)).symm⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    change e.hom (f z) = p
    rw [hz]
    exact (Scheme.homeoOfIso e).right_inv p

/-- Source and target reindexing preserve the exact original chart range. -/
theorem arithmeticBoundary_range_betweenIso {A B C D : Scheme}
    (e : A ≅ B) (f : A ⟶ C) (g : C ≅ D) (p : D) :
    p ∈ Set.range ((e.inv ≫ f) ≫ g.hom) ↔ g.inv p ∈ Set.range f := by
  rw [arithmeticBoundary_range_targetIso]
  exact (congrArg (fun s => g.inv p ∈ s)
    (SchemeOpenChartRange.range_iso_comp e.symm f)).to_iff

/-- An isomorphism detects membership in the image of any preceding morphism. -/
theorem arithmeticBoundary_range_comp_iso {A B C : Scheme}
    (f : A ⟶ B) (e : B ⟶ C) [IsIso e] (p : B) :
    p ∈ Set.range f ↔ e p ∈ Set.range (f ≫ e) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, (Scheme.homeoOfIso (asIso e)).injective hz⟩

end FLT.Mazur.WeierstrassDividedDepth

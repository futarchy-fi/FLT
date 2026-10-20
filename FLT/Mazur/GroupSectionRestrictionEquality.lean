/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupSectionBaseChange

/-!
# Exact restriction equalities and actual pulled-back sections

Equality after restricting original scheme maps is equivalent to equality of
sections in the actual fiber product. This retains the original projections
and works for every base map, without reducedness or flatness assumptions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GroupSectionBaseChange
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (k : T ⟶ S) {G X : Over S}

/-- Pullback section equality is exactly equality of restricted original scheme maps. -/
theorem pullSection_eq_iff (p q : 𝟙_ (Over S) ⟶ X) :
    pullSection k p = pullSection k q ↔ k ≫ p.left = k ≫ q.left := by
  constructor
  · intro h
    have he := congrArg (fun z => z.left ≫ pullback.fst X.hom k) h
    simpa only [section_fst] using he
  · intro h
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa only [section_fst] using h
    · exact (pullSection k p).w.trans (pullSection k q).w.symm

/-- Restricted equality transports through the original base-changed comparison. -/
theorem pullSection_comp_eq (p : 𝟙_ (Over S) ⟶ G) (q : 𝟙_ (Over S) ⟶ X)
    (f : G ⟶ X) (h : k ≫ p.left ≫ f.left = k ≫ q.left) :
    pullSection k p ≫ (Over.pullback k).map f = pullSection k q := by
  rw [← section_comp]
  exact (pullSection_eq_iff k (p ≫ f) q).mpr h

end FLT.Mazur.GroupSectionBaseChange

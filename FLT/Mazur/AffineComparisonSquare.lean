/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Transporting comparison squares through object presentations

Conjugating the four edges by object isomorphisms preserves a commuting square.
This permits independent object presentations without expanding their definitions.
-/

@[expose] public section
open CategoryTheory
namespace FLT.Mazur.AffineComparisonSquare

/-- A square remains commutative after changing the presentations of all four objects. -/
theorem of_presentations {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {a b a₀ b₀ : A} {c d c₀ d₀ : B}
    (e : a ≅ b) (f : c ≅ d) (l : F.obj a ≅ c) (r : F.obj b ≅ d)
    (e₀ : a₀ ≅ b₀) (f₀ : c₀ ≅ d₀) (l₀ : F.obj a₀ ≅ c₀) (r₀ : F.obj b₀ ≅ d₀)
    (na : a ≅ a₀) (nb : b ≅ b₀) (nc : c ≅ c₀) (nd : d ≅ d₀)
    (he : e ≪≫ nb = na ≪≫ e₀) (hf : f ≪≫ nd = nc ≪≫ f₀)
    (hl : l ≪≫ nc = F.mapIso na ≪≫ l₀) (hr : r ≪≫ nd = F.mapIso nb ≪≫ r₀)
    (h : F.map e₀.hom ≫ r₀.hom = l₀.hom ≫ f₀.hom) :
    F.map e.hom ≫ r.hom = l.hom ≫ f.hom := by
  have heh := congrArg Iso.hom he
  have hfh := congrArg Iso.hom hf
  have hlh := congrArg Iso.hom hl
  have hrh := congrArg Iso.hom hr
  simp only [Iso.trans_hom, Functor.mapIso_hom] at heh hfh hlh hrh
  apply (cancel_mono nd.hom).mp
  rw [Category.assoc, hrh, ← Category.assoc, ← F.map_comp, heh, F.map_comp,
    Category.assoc, h, ← Category.assoc, ← hlh, Category.assoc, ← hfh, ← Category.assoc]

end FLT.Mazur.AffineComparisonSquare

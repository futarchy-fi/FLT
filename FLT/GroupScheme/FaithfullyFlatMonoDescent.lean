/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Monomorphisms descend through a faithfully flat scheme cover

Pulling two test maps back to the cover makes them equal by monicity upstairs.
The faithfully flat test cover is an epimorphism, so the original maps agree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.GroupScheme

/-- A morphism whose faithfully flat base change is monic is itself monic. -/
theorem mono_of_faithfullyFlat_pullback {X Y X' Y' : Scheme}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X}
    (h : IsPullback f' p g f) [Flat g] [Surjective g] [Mono f'] : Mono f := by
  constructor
  intro T a b hab
  let r : pullback (a ≫ f) g ⟶ T := pullback.fst _ _
  let s : pullback (a ≫ f) g ⟶ Y' := pullback.snd _ _
  have ha : s ≫ g = (r ≫ a) ≫ f := by
    simpa only [r, s, Category.assoc] using (pullback.condition (f := a ≫ f) (g := g)).symm
  have hb : s ≫ g = (r ≫ b) ≫ f := by
    rw [Category.assoc, ← hab, ← Category.assoc]
    exact ha
  have he : h.lift s (r ≫ a) ha = h.lift s (r ≫ b) hb := by
    apply (cancel_mono f').mp
    rw [h.lift_fst, h.lift_fst]
  let _ : Epi r := Flat.epi_of_flat_of_surjective r
  apply (cancel_epi r).mp
  exact (h.lift_snd s (r ≫ a) ha).symm.trans
    ((congrArg (fun u ↦ u ≫ p) he).trans (h.lift_snd s (r ≫ b) hb))

end FLT.GroupScheme

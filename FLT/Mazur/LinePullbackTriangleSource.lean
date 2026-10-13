/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineSectionTriangle

/-!
# Changing the source line of a pullback triangle

Replacing a line on the base by an isomorphic descended line preserves the
actual comparison triangle, including the compositor and map-equality transport.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
variable {X Y Z : Scheme} {f : X ⟶ Y} {g : Y ⟶ Z} {r : X ⟶ Z}
  {w : f ≫ g = r} {A A' : Z.Modules} {B : Y.Modules} {C : X.Modules}
  {e : (pullback g).obj A ≅ B} {v : (pullback f).obj B ≅ C}
  {k : (pullback r).obj A ≅ C}

/-- A specified source isomorphism preserves the exact pullback triangle. -/
theorem LinePullbackTriangle.sourceIso (he : LinePullbackTriangle f g r w e v k)
    (a : A' ≅ A) :
    LinePullbackTriangle f g r w ((pullback g).mapIso a ≪≫ e) v
      ((pullback r).mapIso a ≪≫ k) := by
  apply Iso.ext
  have hh := congrArg Iso.hom he
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom] at hh ⊢
  have hn := (pullbackComp f g).inv.naturality a.hom
  dsimp only [Functor.comp_map] at hn
  rw [Functor.map_comp, ← Category.assoc, ← Category.assoc, ← hn]
  simp only [Category.assoc]
  rw [hh, ← Category.assoc, (pullbackCongr w).hom.naturality a.hom]
  simp only [Category.assoc]

end FLT.Mazur.FCurve

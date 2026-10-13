/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFppfLocallyRingedCover

/-!
# Actual relative scheme morphisms descend along fppf covers

Descent retains the coefficient morphism and the entire locally ringed map.
Compatibility is checked on the actual scheme kernel pair.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeFppfSchemeCover
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {U T Z : Over S} (g : U ⟶ T)
  [Flat g.left] [LocallyOfFinitePresentation g.left] [Surjective g.left]
  (a : U ⟶ Z) (ha : pullback.fst g g ≫ a = pullback.snd g g ≫ a)

/-- The descended scheme morphism, before checking its original coefficient map. -/
def schemeDescend : T.left ⟶ Z.left :=
  ⟨RelativeFppfLocallyRingedCover.descend g a.left.toLRSHom (by
    simpa only [Over.comp_left, Scheme.Hom.comp_toLRSHom] using
      congrArg (fun b ↦ b.left.toLRSHom) ha)⟩

/-- The actual source cover recovers the original scheme morphism. -/
@[reassoc]
theorem schemeDescend_source : g.left ≫ schemeDescend g a ha = a.left := by
  apply Scheme.Hom.ext'
  exact RelativeFppfLocallyRingedCover.descend_projection _ _ _

/-- Scheme descent retains precisely the original coefficient morphism. -/
theorem schemeDescend_base : schemeDescend g a ha ≫ Z.hom = T.hom := by
  apply (cancel_epi g.left).mp
  rw [schemeDescend_source_assoc, Over.w, Over.w]

/-- Descent in schemes over the original base. -/
def descend : T ⟶ Z := Over.homMk (schemeDescend g a ha) (schemeDescend_base g a ha)

/-- The descended relative map has its prescribed source equation. -/
@[reassoc]
theorem descend_source : g ≫ descend g a ha = a := by
  ext
  exact schemeDescend_source g a ha

/-- Descent is unique as an actual relative scheme morphism. -/
theorem descend_unique (b : T ⟶ Z) (hb : g ≫ b = a) : b = descend g a ha := by
  apply (Over.forget S).map_injective
  apply (cancel_epi g.left).mp
  exact (congrArg Over.Hom.left hb).trans (schemeDescend_source g a ha).symm

/-- Postcomposition commutes with the constructed descent, including the structure maps. -/
theorem descend_comp {Y : Over S} (b : Z ⟶ Y) :
    descend g a ha ≫ b = descend g (a ≫ b) (by rw [← Category.assoc, ha, Category.assoc]) :=
  descend_unique g _ _ _ (by rw [descend_source_assoc])

include ha in
/-- No second target map can give a different factorization of the same source map. -/
theorem existsUnique : ∃! b : T ⟶ Z, g ≫ b = a :=
  ⟨descend g a ha, descend_source g a ha, fun b hb ↦ descend_unique g a ha b hb⟩

end FLT.Mazur.RelativeFppfSchemeCover

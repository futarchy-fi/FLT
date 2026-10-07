/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOverlapProjectionComposition
public import FLT.Mazur.SchemeGeometricDescentData

/-!
# Composition coherence of geometric scheme descent data

The cover pullback composition isomorphism intertwines successive refinement
and direct refinement along the composite square. This follows from the actual
projection comparisons, without a coherence hypothesis on the descent datum.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeOverlapRefinement
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y X' Y' X'' Y'' : Scheme.{u}}
variable (p : Y ⟶ X) (q : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
variable (w : q ≫ a = b ≫ p)
variable (r : Y'' ⟶ X'') (c : X'' ⟶ X') (d : Y'' ⟶ Y')
variable (v : r ≫ c = d ≫ q)
variable {M : Y.Modules}

/-- Successive and composite refined overlaps agree under the cover composition chart. -/
@[reassoc]
theorem refine_composition (e : (pullback (Limits.pullback.fst p p)).obj M ≅
    (pullback (Limits.pullback.snd p p)).obj M) :
    (refine q r c d v (refine p q a b w e)).hom ≫
        (pullback (Limits.pullback.snd r r)).map ((pullbackComp d b).hom.app M) =
      (pullback (Limits.pullback.fst r r)).map ((pullbackComp d b).hom.app M) ≫
        (refine p r (c ≫ a) (d ≫ b) (square_comp p q a b w r c d v) e).hom := by
  have hn := (overlapCompositionIso p q a b w r c d v).hom.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  have h₁ := refine_hom p q a b w e
  have h₂ := refine_hom q r c d v (refine p q a b w e)
  have h₃ := refine_hom p r (c ≫ a) (d ≫ b) (square_comp p q a b w r c d v) e
  dsimp only [Iso.app_hom] at h₁ h₂ h₃
  apply (cancel_mono
    ((secondIso p r (c ≫ a) (d ≫ b) (square_comp p q a b w r c d v)).hom.app M)).mp
  simp only [Category.assoc]
  rw [secondIso_composition p q a b w r c d v, h₃]
  rw [← Category.assoc (refine q r c d v (refine p q a b w e)).hom, h₂]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, h₁, Functor.map_comp]
  simp only [Category.assoc]
  rw [hn]
  rw [firstIso_composition_assoc p q a b w r c d v]

end FLT.Mazur.SchemeOverlapRefinement

namespace FLT.Mazur.SchemeGeometricDescent.Data
open SchemeOverlapRefinement
variable {X Y X' Y' X'' Y'' : Scheme.{u}}
variable (p : Y ⟶ X) (q : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
variable (w : q ≫ a = b ≫ p)
variable (r : Y'' ⟶ X'') (c : X'' ⟶ X') (d : Y'' ⟶ Y')
variable (v : r ≫ c = d ≫ q)
variable {M : Y.Modules} (D : Data p M)

/-- The actual cover composition chart is a compatible map of scheme descent data. -/
theorem refine_composition_compatible :
    ((D.refine p q a b w).refine q r c d v).MapCompatible r
      (D.refine p r (c ≫ a) (d ≫ b) (square_comp p q a b w r c d v))
      ((pullbackComp d b).hom.app M) :=
  refine_composition p q a b w r c d v D.overlap

end FLT.Mazur.SchemeGeometricDescent.Data

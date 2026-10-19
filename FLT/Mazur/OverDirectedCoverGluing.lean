/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Gluing relative maps on a directed base cover

Maps of the actual pullbacks glue when their projections agree under cover
refinement. Recovery and uniqueness hold in the original slice category.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OverDirectedCoverGluing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (C : S.OpenCover) {X Y : Over S}

/-- Pullback along an open cover jointly detects relative maps. -/
theorem hom_ext (a b : X ⟶ Y)
    (h : ∀ i, (Over.pullback (C.f i)).map a = (Over.pullback (C.f i)).map b) : a = b := by
  apply Over.OverMorphism.ext
  apply Scheme.Cover.hom_ext (C.pullback₁ X.hom)
  intro i
  change pullback.fst X.hom (C.f i) ≫ a.left =
    pullback.fst X.hom (C.f i) ≫ b.left
  have hi := congrArg (fun z ↦ z.left ≫ pullback.fst Y.hom (C.f i)) (h i)
  simpa only [Over.pullback_map_left, pullback.lift_fst, Category.comp_id] using hi

variable [Category* C.I₀] [C.LocallyDirected]
  (a : ∀ i, (Over.pullback (C.f i)).obj X ⟶ (Over.pullback (C.f i)).obj Y)

/-- The projected maps agree on every actual refinement of the base cover. -/
def Compatible : Prop :=
  ∀ {i j : C.I₀} (h : i ⟶ j),
    Scheme.Cover.trans (C.pullback₁ X.hom) h ≫ (a j).left ≫ pullback.fst Y.hom (C.f j) =
      (a i).left ≫ pullback.fst Y.hom (C.f i)

variable (ha : Compatible C a)

/-- Glue the actual relative maps, retaining their prescribed base morphism. -/
def glue : X ⟶ Y :=
  Scheme.OpenCover.glueMorphismsOverOfLocallyDirected (C.pullback₁ X.hom)
    (fun i ↦ (a i).left ≫ pullback.fst Y.hom (C.f i)) ha (fun i ↦ by
      have hw := (a i).w
      change (a i).left ≫ pullback.snd Y.hom (C.f i) =
        pullback.snd X.hom (C.f i) at hw
      change (_ ≫ pullback.fst Y.hom (C.f i)) ≫ Y.hom =
        pullback.fst X.hom (C.f i) ≫ X.hom
      rw [Category.assoc, pullback.condition, ← Category.assoc, hw, pullback.condition])

/-- The glued map has the specified original-space projection on every chart. -/
@[reassoc] theorem glue_fst (i : C.I₀) :
    pullback.fst X.hom (C.f i) ≫ (glue C a ha).left =
      (a i).left ≫ pullback.fst Y.hom (C.f i) :=
  Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left (C.pullback₁ X.hom) _ _ _ i

/-- Pullback of the glued map recovers each entire relative map. -/
theorem glue_map (i : C.I₀) : (Over.pullback (C.f i)).map (glue C a ha) = a i := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa only [Over.pullback_map_left, pullback.lift_fst, Category.comp_id] using
      glue_fst C a ha i
  · exact ((Over.pullback (C.f i)).map (glue C a ha)).w.trans (a i).w.symm

include ha in
/-- A compatible local family has exactly one original relative map. -/
theorem glue_unique : ∃! f : X ⟶ Y, ∀ i, (Over.pullback (C.f i)).map f = a i := by
  refine ⟨glue C a ha, glue_map C a ha, fun f hf ↦ ?_⟩
  exact hom_ext C f (glue C a ha) (fun i ↦ (hf i).trans (glue_map C a ha i).symm)

end FLT.Mazur.OverDirectedCoverGluing

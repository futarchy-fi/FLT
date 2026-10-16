/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedFrameFree
public import FLT.Mazur.EquivalenceRelationNormalizedLabelChange
public import FLT.Mazur.RelativeDistinctSubframe

/-!
# Moving subframes of the entire original relation

Select any injective family of labels, then use its distinguished coordinate as
the new first endpoint. The resulting scheme map retains every selected second
endpoint, and its first endpoints are connected by the actual original arrow.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J H : Type} [Fintype I] [Fintype J] [Fintype H] (o : I) (o' : J)

local instance subframeOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›

/-- Select an arbitrary subframe and normalize it at its own distinguished label. -/
def subframeMap (ι : J ↪ I) : source p q I o ⟶ source p q J o' :=
  lift p q J o' (labelFrame e I o (ι o') ≫ subframe (Over.mk p) ι) (by
    rw [Category.assoc, subframe_coordinate]
    exact (labelFrame_second e I o (ι o') (ι o')).symm)

/-- The new first endpoint is the selected distinguished original second endpoint. -/
@[reassoc] theorem subframeMap_first (ι : J ↪ I) :
    subframeMap e o o' ι ≫ first p q J o' = coordinate p q I o (ι o') ≫ q :=
  lift_first p q J o' _ _

/-- Selection retains actual second endpoint morphisms, including on nonreduced tests. -/
@[reassoc] theorem subframeMap_second (ι : J ↪ I) (j : J) :
    subframeMap e o o' ι ≫ coordinate p q J o' j ≫ q =
      coordinate p q I o (ι j) ≫ q := by
  rw [← Category.assoc, subframeMap, lift_coordinate, Category.assoc, subframe_coordinate]
  exact labelFrame_second e I o (ι o') (ι j)

/-- Successive moving subframes agree with the composite label selection. -/
theorem subframeMap_comp (o'' : H) (ι : J ↪ I) (κ : H ↪ J) :
    subframeMap e o o' ι ≫ subframeMap e o' o'' κ =
      subframeMap e o o'' (κ.trans ι) := by
  apply hom_ext_second p q H o'' e
  intro j
  simp only [Category.assoc, subframeMap_second, Function.Embedding.trans_apply]

/-- Selecting all labels without changing the distinguished one is the identity. -/
theorem subframeMap_refl : subframeMap e o o (Function.Embedding.refl I) = 𝟙 _ := by
  apply hom_ext_second p q I o e
  intro i
  rw [subframeMap_second, Category.id_comp]
  rfl

/-- Selecting all labels with a different distinguished one recovers canonical transport. -/
theorem subframeMap_label (j : I) :
    subframeMap e o j (Function.Embedding.refl I) = labelChange e I o j := by
  apply hom_ext_second p q I j e
  intro i
  rw [subframeMap_second, labelChange_second]
  rfl

include e in
/-- On a nonempty test, the smaller resulting frame determines its label embedding uniquely. -/
theorem subframeMap_unique {T : Scheme} [Nonempty T] (u : T ⟶ source p q I o)
    (ι κ : J ↪ I) (h : u ≫ subframeMap e o o' ι = u ≫ subframeMap e o o' κ) : ι = κ := by
  ext j
  apply second_injective e I o u
  have hj := congrArg (fun f ↦ f ≫ coordinate p q J o' j ≫ q) h
  simpa only [Category.assoc, subframeMap_second] using hj

end FLT.Mazur.EquivalenceRelationNormalizedFrames

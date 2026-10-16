/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationMixedFrameRelation
public import FLT.Mazur.EquivalenceRelationNormalizedLabelChange

/-!
# Transporting the whole mixed relation between distinguished labels

The second frame changes label by its canonical scheme isomorphism. Composing
the original arrow with the actual label arrow retains every related pair.
The inverse transport proves this is an isomorphism of entire relation schemes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
open EquivalenceRelationFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  (I J : Type) [Fintype I] [Fintype J] (o : I) (o' o'' : J)

/-- Transport the original relation arrow along the second frame's label change. -/
def retargetArrow : relation p q I J o o' ⟶ D :=
  compose e (arrow p q I J o o') (snd p q I J o o' ≫ coordinate p q J o' o'') (by
    rw [Category.assoc, coordinate_first, arrow_second])

/-- The original first endpoint is unchanged by target-label transport. -/
@[reassoc] theorem retargetArrow_first :
    retargetArrow e I J o o' o'' ≫ p = fst p q I J o o' ≫ first p q I o := by
  rw [retargetArrow, compose_fst, arrow_first]

/-- The original second endpoint is moved by its actual label arrow. -/
@[reassoc] theorem retargetArrow_second :
    retargetArrow e I J o o' o'' ≫ q =
      (snd p q I J o o' ≫ labelChange e J o' o'') ≫ first p q J o'' := by
  simp only [retargetArrow, compose_snd, Category.assoc, labelChange_first]

/-- Transport the entire original mixed relation to a new target label. -/
def retarget : relation p q I J o o' ⟶ relation p q I J o o'' :=
  lift p q I J o o'' (fst p q I J o o')
    (snd p q I J o o' ≫ labelChange e J o' o'') (retargetArrow e I J o o' o'')
    (retargetArrow_first e I J o o' o'') (retargetArrow_second e I J o o' o'')

/-- Target-label transport retains the first frame exactly. -/
@[reassoc] theorem retarget_fst :
    retarget e I J o o' o'' ≫ fst p q I J o o'' = fst p q I J o o' :=
  lift_fst p q I J o o'' _ _ _ _ _

/-- Target-label transport uses the canonical label isomorphism on the second frame. -/
@[reassoc] theorem retarget_snd :
    retarget e I J o o' o'' ≫ snd p q I J o o'' =
      snd p q I J o o' ≫ labelChange e J o' o'' :=
  lift_snd p q I J o o'' _ _ _ _ _

/-- Every original arrow is transported by actual relation composition. -/
@[reassoc] theorem retarget_arrow :
    retarget e I J o o' o'' ≫ arrow p q I J o o'' = retargetArrow e I J o o' o'' :=
  lift_arrow p q I J o o'' _ _ _ _ _

/-- Successive target-label transports agree with direct transport on the whole relation. -/
theorem retarget_comp (o''' : J) :
    retarget e I J o o' o'' ≫ retarget e I J o o'' o''' = retarget e I J o o' o''' := by
  apply hom_ext p q I J o o''' e
  · simp only [Category.assoc, retarget_fst]
  · simp only [Category.assoc, retarget_snd, retarget_snd_assoc, labelChange_comp]

/-- Transport to the same target label is the identity on every original relation arrow. -/
theorem retarget_self : retarget e I J o o' o' = 𝟙 _ := by
  apply hom_ext p q I J o o' e
  · rw [retarget_fst, Category.id_comp]
  · rw [retarget_snd, labelChange_self, Category.comp_id, Category.id_comp]

/-- Changing the target label identifies the entire original mixed relation schemes. -/
def retargetIso : relation p q I J o o' ≅ relation p q I J o o'' where
  hom := retarget e I J o o' o''
  inv := retarget e I J o o'' o'
  hom_inv_id := by rw [retarget_comp, retarget_self]
  inv_hom_id := by rw [retarget_comp, retarget_self]

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames

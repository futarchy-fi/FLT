/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedFrameAction

/-!
# Changing the distinguished label of a normalized frame

Rebase the entire frame to the newly distinguished coordinate. This gives an
actual scheme isomorphism between the different normalized sources, retaining
every second endpoint and the original arrow between the first endpoints.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples EquivalenceRelationOrderedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o o' : I)

local instance labelOverFirst_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›

/-- The whole original frame rebased to the new distinguished endpoint. -/
def labelFrame : Over.mk (coordinate p q I o o' ≫ q) ⟶ distinctScheme (Over.mk p) I :=
  rebaseFrame e I (coordinate p q I o o')
    (frameCast I (coordinate_first p q I o o').symm (frame p q I o))

/-- Rebasing to a different distinguished label keeps all second endpoints. -/
@[reassoc] theorem labelFrame_second (i : I) :
    (labelFrame e I o o' ≫ distinctCoordinate (Over.mk p) I i).left ≫ q =
      coordinate p q I o i ≫ q :=
  rebaseFrame_second e I _ _ i

/-- The morphism between normalized sources with independent distinguished labels. -/
def labelChange : source p q I o ⟶ source p q I o' :=
  lift p q I o' (labelFrame e I o o') (labelFrame_second e I o o' o').symm

/-- The new first endpoint is the old coordinate with the new distinguished label. -/
@[reassoc] theorem labelChange_first :
    labelChange e I o o' ≫ first p q I o' = coordinate p q I o o' ≫ q :=
  lift_first p q I o' _ _

/-- Every original second endpoint is unchanged as a scheme morphism. -/
@[reassoc] theorem labelChange_second (i : I) :
    labelChange e I o o' ≫ coordinate p q I o' i ≫ q = coordinate p q I o i ≫ q := by
  rw [← Category.assoc, labelChange, lift_coordinate, labelFrame_second]

/-- Changing a label twice agrees exactly with the direct change. -/
theorem labelChange_comp (o'' : I) :
    labelChange e I o o' ≫ labelChange e I o' o'' = labelChange e I o o'' := by
  apply hom_ext_second p q I o'' e
  intro i
  simp only [Category.assoc, labelChange_second]

/-- Keeping the distinguished label gives the identity morphism. -/
theorem labelChange_self : labelChange e I o o = 𝟙 _ := by
  apply hom_ext_second p q I o e
  intro i
  rw [labelChange_second, Category.id_comp]

/-- All choices of distinguished label give canonically isomorphic schemes. -/
def labelIso : source p q I o ≅ source p q I o' where
  hom := labelChange e I o o'
  inv := labelChange e I o' o
  hom_inv_id := by rw [labelChange_comp, labelChange_self]
  inv_hom_id := by rw [labelChange_comp, labelChange_self]

/-- The label transition uses an unchanged original relation coordinate. -/
@[reassoc] theorem labelChange_arrow_first :
    coordinate p q I o o' ≫ p = first p q I o := coordinate_first p q I o o'

/-- The same original arrow ends at the changed normalized first endpoint. -/
@[reassoc] theorem labelChange_arrow_second :
    coordinate p q I o o' ≫ q = labelChange e I o o' ≫ first p q I o' :=
  (labelChange_first e I o o').symm

end FLT.Mazur.EquivalenceRelationNormalizedFrames

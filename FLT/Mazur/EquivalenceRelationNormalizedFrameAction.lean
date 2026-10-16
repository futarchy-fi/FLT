/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedFrames

/-!
# Permutations that move the original first endpoint

Permute the labels and rebase the whole original frame to the newly distinguished
endpoint. The normalized frame scheme carries the resulting genuine finite-group
action. Its first endpoint moves along an actual original relation arrow.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples EquivalenceRelationOrderedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)

local instance actionOverFirst_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local notation "F" => distinctScheme (Over.mk p) I
local notation "N" => source p q I o

/-- Rebase to the endpoint which will become distinguished after relabeling. -/
def movedFrame (σ : Equiv.Perm I) :
    Over.mk (coordinate p q I o (σ.symm o) ≫ q) ⟶ F :=
  rebaseFrame e I (coordinate p q I o (σ.symm o))
    (frameCast I (coordinate_first p q I o (σ.symm o)).symm (frame p q I o))

/-- Relabel the entire rebased frame. -/
def permutedFrame (σ : Equiv.Perm I) :
    Over.mk (coordinate p q I o (σ.symm o) ≫ q) ⟶ F :=
  Over.homMk ((movedFrame e I o σ).left ≫ (distinctAction (Over.mk p) I σ).hom) (by
    rw [Category.assoc, distinctAction_base]
    exact (movedFrame e I o σ).w)

/-- Every original second endpoint is permuted, with its full scheme structure retained. -/
@[reassoc] theorem permutedFrame_second (σ : Equiv.Perm I) (i : I) :
    (permutedFrame e I o σ ≫ distinctCoordinate (Over.mk p) I i).left ≫ q =
      coordinate p q I o (σ.symm i) ≫ q := by
  change (((movedFrame e I o σ).left ≫ (distinctAction (Over.mk p) I σ).hom) ≫
    (distinctCoordinate (Over.mk p) I i).left) ≫ q = _
  simp only [Category.assoc, distinctAction_coordinate_assoc]
  exact rebaseFrame_second e I (coordinate p q I o (σ.symm o))
    (frameCast I (coordinate_first p q I o (σ.symm o)).symm (frame p q I o)) (σ.symm i)

/-- The actual normalized-frame morphism for an original permutation. -/
def actionMap (σ : Equiv.Perm I) : N ⟶ N :=
  lift p q I o (permutedFrame e I o σ) (permutedFrame_second e I o σ o).symm

/-- The new first endpoint is the original selected second endpoint. -/
@[reassoc] theorem actionMap_first (σ : Equiv.Perm I) :
    actionMap e I o σ ≫ first p q I o = coordinate p q I o (σ.symm o) ≫ q :=
  lift_first p q I o _ _

/-- The action permutes all second endpoints while also moving the first endpoint. -/
@[reassoc] theorem actionMap_second (σ : Equiv.Perm I) (i : I) :
    actionMap e I o σ ≫ coordinate p q I o i ≫ q =
      coordinate p q I o (σ.symm i) ≫ q := by
  rw [← Category.assoc, actionMap, lift_coordinate, permutedFrame_second]

/-- The identity permutation is the identity on the normalized scheme. -/
theorem actionMap_one : actionMap e I o 1 = 𝟙 N := by
  apply hom_ext_second p q I o e
  intro i
  rw [actionMap_second, Category.id_comp]
  rfl

/-- Composition follows the usual automorphism-group multiplication convention. -/
theorem actionMap_mul (σ τ : Equiv.Perm I) :
    actionMap e I o (σ * τ) = actionMap e I o τ ≫ actionMap e I o σ := by
  apply hom_ext_second p q I o e
  intro i
  rw [actionMap_second, Category.assoc, actionMap_second, actionMap_second]
  rfl

/-- Each normalized permutation map is an actual scheme automorphism. -/
def actionAut (σ : Equiv.Perm I) : Aut N where
  hom := actionMap e I o σ
  inv := actionMap e I o σ⁻¹
  hom_inv_id := by rw [← actionMap_mul, inv_mul_cancel, actionMap_one]
  inv_hom_id := by rw [← actionMap_mul, mul_inv_cancel, actionMap_one]

/-- The finite permutation group acts by rebasing to the newly distinguished endpoint. -/
def action : Equiv.Perm I →* Aut N where
  toFun := actionAut e I o
  map_one' := by
    apply Aut.ext
    exact actionMap_one e I o
  map_mul' σ τ := by
    apply Aut.ext
    exact actionMap_mul e I o σ τ

/-- The action's endpoint transition is itself an original relation arrow. -/
def actionArrow (σ : Equiv.Perm I) : N ⟶ D := coordinate p q I o (σ.symm o)

/-- The transition starts at the original first endpoint. -/
@[reassoc] theorem actionArrow_first (σ : Equiv.Perm I) :
    actionArrow (p := p) (q := q) I o σ ≫ p = first p q I o := coordinate_first p q I o _

/-- The transition ends at the moved first endpoint. -/
@[reassoc] theorem actionArrow_second (σ : Equiv.Perm I) :
    actionArrow (p := p) (q := q) I o σ ≫ q = (action e I o σ).hom ≫ first p q I o :=
  (actionMap_first e I o σ).symm

end FLT.Mazur.EquivalenceRelationNormalizedFrames

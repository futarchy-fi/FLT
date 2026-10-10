/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentCanonicalOverlap
public import FLT.Mazur.SchemeIndependentTripleCocycle

/-!
# Canonical unequal pair overlaps satisfy the original triple law

Each edge normalizes through the same base map on the original triple.
The common middle comparison cancels, giving the required cocycle.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeIndependentCanonicalOverlap
open SchemeFamilyTripleOverlap SchemeIndependentTripleCocycle
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y₁ Y₂ Y₃ : Scheme.{u}}

/-- The canonical isomorphism on the original unequal fiber product. -/
def pair (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) (A : X.Modules) :
    (pullback (Limits.pullback.fst f g)).obj ((pullback f).obj A) ≅
      (pullback (Limits.pullback.snd f g)).obj ((pullback g).obj A) :=
  overlap f g _ _ (Limits.pullback.fst f g ≫ f) rfl Limits.pullback.condition.symm A

/-- Canonical overlaps satisfy the unequal triple cocycle without assembled inputs. -/
lemma pair_cocycle (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) (h : Y₃ ⟶ X) (A : X.Modules) :
    Cocycle f g h ((pullback f).obj A) ((pullback g).obj A) ((pullback h).obj A)
      (pair f g A) (pair g h A) (pair f h A) := by
  have h2 : coord2 f g h ≫ g = coord1 f g h ≫ f := by
    dsimp only [coord1, coord2]
    rw [Category.assoc, Category.assoc]
    exact congrArg (fun q ↦ pair12 f g h ≫ q) (Limits.pullback.condition (f := f) (g := g)).symm
  have h3 : coord3 f g h ≫ h = coord1 f g h ≫ f := (coord13_base f g h).symm
  dsimp only [Cocycle, edge12, edge23, edge13, pair]
  rw [normalize_overlap f g _ _ _ rfl Limits.pullback.condition.symm
      (pair12 f g h) _ _ rfl rfl (coord1 f g h ≫ f) rfl h2,
    normalize_overlap g h _ _ _ rfl Limits.pullback.condition.symm
      (pair23 f g h) _ _ (pair23_fst f g h) rfl (coord1 f g h ≫ f) h2 h3,
    normalize_overlap f h _ _ _ rfl Limits.pullback.condition.symm
      (pair13 f g h) _ _ (pair13_fst f g h) (pair13_snd f g h)
      (coord1 f g h ≫ f) rfl h3]
  simp only [overlap, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

end FLT.Mazur.SchemeIndependentCanonicalOverlap

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedRestriction

/-!
# Restriction of the actual closed graded coefficients

The direct sum of the original closed coefficient restrictions is naturally
isomorphic to the additive presheaf of ambient graded coefficients. Each
homogeneous summand keeps its original closed sheaf restriction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open FLT.Mazur.IdealAdicGradedSections FLT.Mazur.IdealAdicQuotient

universe u

namespace FLT.Mazur.IdealAdicGradedClosedAction

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)

/-- The actual closed sheaf restriction in one coefficient degree. -/
def pieceRestriction {U V : X.Opens} (i : U ⟶ V) (n : ℕ) :
    ClosedPiece I V n →+ ClosedPiece I U n :=
  ((closedIdealGraded I n).presheaf.map
    ((TopologicalSpace.Opens.map I.subschemeι.base).map i).op).hom

set_option maxRecDepth 2048 in
/-- Degreewise comparison preserves the original closed sheaf restriction. -/
lemma pieceEquiv_restrict {U V : X.Opens} (i : U ⟶ V) (n : ℕ)
    (s : ClosedPiece I V n) :
    pieceEquiv I U n (pieceRestriction I i n s) =
      (idealGraded I n).presheaf.map i.op (pieceEquiv I V n s) :=
  PresheafOfModules.naturality_apply (closedIdealGradedIso I n).hom.val i.op s

/-- Restriction of the direct sum of the actual closed coefficients. -/
def totalRestriction {U V : X.Opens} (i : U ⟶ V) : Total I V →+ Total I U :=
  DirectSum.map (pieceRestriction I i)

/-- Total restriction keeps the original homogeneous closed restriction. -/
lemma totalRestriction_of {U V : X.Opens} (i : U ⟶ V) (n : ℕ)
    (s : ClosedPiece I V n) :
    totalRestriction I i (DirectSum.of (ClosedPiece I V) n s) =
      DirectSum.of (ClosedPiece I U) n (pieceRestriction I i n s) :=
  DirectSum.map_of _ n s

/-- The canonical closed-to-ambient comparison is natural in the open. -/
lemma totalEquiv_restrict {U V : X.Opens} (i : U ⟶ V) (s : Total I V) :
    totalEquiv I U (totalRestriction I i s) =
      restrict I U i (totalEquiv I V s) := by
  induction s using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add s t hs ht => simp only [map_add, hs, ht]
  | of n s =>
    rw [totalRestriction_of, totalEquiv_of, totalEquiv_of, restrict_of,
      pieceEquiv_restrict]

/-- Identity fixes every total closed coefficient. -/
lemma totalRestriction_id (U : X.Opens) (s : Total I U) :
    totalRestriction I (𝟙 U) s = s := by
  apply (totalEquiv I U).injective
  rw [totalEquiv_restrict]
  exact RingHom.congr_fun (restrict_id I U) (totalEquiv I U s)

/-- Total closed coefficient restrictions compose. -/
lemma totalRestriction_comp {U V W : X.Opens} (i : U ⟶ V) (j : V ⟶ W)
    (s : Total I W) :
    totalRestriction I i (totalRestriction I j s) = totalRestriction I (i ≫ j) s := by
  apply (totalEquiv I U).injective
  rw [totalEquiv_restrict, totalEquiv_restrict, totalEquiv_restrict]
  exact RingHom.congr_fun (restrict_comp I i j) (totalEquiv I W s)

/-- The actual closed total coefficients form an additive presheaf. -/
def totalPresheaf : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (Total I U.unop)
  map i := AddCommGrpCat.ofHom (totalRestriction I i.unop)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro s
    exact totalRestriction_id I U.unop s
  map_comp i j := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (totalRestriction_comp I j.unop i.unop s).symm

/-- The actual closed total presheaf identifies with ambient graded coefficients. -/
def totalPresheafIso :
    totalPresheaf I ≅ ringPresheaf I ⋙ forget₂ _ RingCat ⋙ forget₂ _ AddCommGrpCat :=
  NatIso.ofComponents (fun U ↦ (totalEquiv I U.unop).toAddCommGrpIso) (by
    intro U V i
    apply ConcreteCategory.hom_ext
    intro s
    exact totalEquiv_restrict I i.unop s)

end FLT.Mazur.IdealAdicGradedClosedAction

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicLineQuotient
public import FLT.Mazur.BaseAdicThickening
public import FLT.Mazur.AmpleAffinePullback

/-!
# Compatible closed restrictions of powers of a line

The quotient tower identifies with closed restrictions, compatibly with the
original restriction units and every reduction. Pullback of a tensor power
is the tensor power of the pulled-back line, also in degree zero.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite
open Scheme.Modules FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  (I : X.IdealSheafData) (L : X.Modules) [L.IsFinitePresentation]
  (hL : LocallyFreeRankOne L)

/-- The actual closed restriction, considered on the ambient scheme. -/
abbrev closedRestriction (n : ℕ) : X.Modules :=
  (pushforward (I ^ n).subschemeι).obj ((Scheme.Modules.pullback (I ^ n).subschemeι).obj L)

/-- Reduction between closed restrictions, characterized by the original restriction units. -/
def closedReduction {a b : ℕ} (h : a ≤ b) :
    closedRestriction I L b ⟶ closedRestriction I L a :=
  (lineQuotientClosedIso I L hL b).inv ≫ reduction I L h ≫
    (lineQuotientClosedIso I L hL a).hom

/-- The comparison intertwines every quotient reduction. -/
@[reassoc (attr := simp)]
lemma lineQuotientClosedIso_reduction {a b : ℕ} (h : a ≤ b) :
    (lineQuotientClosedIso I L hL b).hom ≫ closedReduction I L hL h =
      reduction I L h ≫ (lineQuotientClosedIso I L hL a).hom := by
  simp [closedReduction]

/-- Reduction of closed restrictions retains the actual adjunction units. -/
@[reassoc (attr := simp)]
lemma unit_closedReduction {a b : ℕ} (h : a ≤ b) :
    (pullbackPushforwardAdjunction (I ^ b).subschemeι).unit.app L ≫
      closedReduction I L hL h =
        (pullbackPushforwardAdjunction (I ^ a).subschemeι).unit.app L := by
  rw [← projection_lineQuotientClosedIso I L hL b, Category.assoc,
    lineQuotientClosedIso_reduction, ← Category.assoc]
  exact (congrArg (fun k ↦ k ≫ (lineQuotientClosedIso I L hL a).hom)
    (projection_reduction I L h)).trans (projection_lineQuotientClosedIso I L hL a)

instance closedReduction_epi {a b : ℕ} (h : a ≤ b) : Epi (closedReduction I L hL h) := by
  dsimp [closedReduction]
  infer_instance

/-- Closed reduction at a repeated index is the identity. -/
@[simp]
lemma closedReduction_refl (n : ℕ) : closedReduction I L hL (le_refl n) = 𝟙 _ := by
  simp [closedReduction]

/-- Closed reductions compose with the original tower indices. -/
@[reassoc (attr := simp)]
lemma closedReduction_trans {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    closedReduction I L hL hbc ≫ closedReduction I L hL hab =
      closedReduction I L hL (hab.trans hbc) := by
  simp only [closedReduction, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (reduction I L hbc), reduction_trans]

/-- Closed restrictions form an inverse system with the canonical reductions. -/
def closedTower : ℕᵒᵖ ⥤ X.Modules where
  obj n := closedRestriction I L n.unop
  map h := closedReduction I L hL (leOfHom h.unop)
  map_id n := closedReduction_refl I L hL n.unop
  map_comp f g := (closedReduction_trans I L hL (leOfHom g.unop) (leOfHom f.unop)).symm

/-- The comparison is an isomorphism of the actual inverse systems. -/
def towerClosedIso : tower I L ≅ closedTower I L hL :=
  NatIso.ofComponents (fun n ↦ lineQuotientClosedIso I L hL n.unop)
    (fun h ↦ (lineQuotientClosedIso_reduction I L hL (leOfHom h.unop)).symm)

omit [IsLocallyNoetherian X] [L.IsFinitePresentation] in
/-- Ideal-adic quotients of tensor powers use tensor powers of the restricted line. -/
def powerQuotientClosedIso (d n : ℕ) :
    quotient I (tensorPower L d) n ≅ (pushforward (I ^ n).subschemeι).obj
      (tensorPower ((Scheme.Modules.pullback (I ^ n).subschemeι).obj L) d) := by
  exact lineQuotientClosedIso I (tensorPower L d) (hL.tensorPower d) n ≪≫
    (pushforward (I ^ n).subschemeι).mapIso
      (ModuleLineBundleTensorPullback.tensorPowerIso (I ^ n).subschemeι L d)

omit [IsLocallyNoetherian X] [L.IsFinitePresentation] in
/-- The tensor-power comparison still starts with the actual restriction unit. -/
@[reassoc]
lemma projection_powerQuotientClosedIso (d n : ℕ) :
    projection I (tensorPower L d) n ≫ (powerQuotientClosedIso I L hL d n).hom =
      (pullbackPushforwardAdjunction (I ^ n).subschemeι).unit.app (tensorPower L d) ≫
        (pushforward (I ^ n).subschemeι).map
          (ModuleLineBundleTensorPullback.tensorPowerIso (I ^ n).subschemeι L d).hom := by
  exact projection_lineQuotientClosedIso_assoc I (tensorPower L d) (hL.tensorPower d) n _

end FLT.Mazur.IdealAdicQuotient

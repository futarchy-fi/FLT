/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodePuncturedDenominatorRestriction
public import FLT.Mazur.PolygonNodeLocalization
public import FLT.Mazur.PrincipalLocalizationPullback

/-!
# The ring maps underlying the punctured node pullbacks

Direct localization of the punctured branch map agrees with restriction first
to the normalization and then to its puncture. Thus the concrete pullback
maps inherit the already proved equality detection statements.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped Polynomial LaurentPolynomial
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PuncturedNodeRestrictionComparison
open LocalizationJointRestriction PolygonNodeEqualizer PolygonNodeLocalization
open PolygonNodePresentation
variable {R : Type u} [CommRing R]

/-- Localization restriction respects composition of ring maps. -/
lemma restriction_comp {S T : Type u} [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (s : R) :
    restriction (g.comp f) s = (restriction g (f s)).comp (restriction f s) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers s)
  apply RingHom.ext
  intro a
  exact (restriction_algebraMap (g.comp f) s a).trans
    ((congrArg (restriction g (f s)) (restriction_algebraMap f s a)).trans
      (restriction_algebraMap g (f s) (f a))).symm

/-- The left affine pullback uses exactly the faithful punctured restriction. -/
lemma left_eq (s : A (R := R)) :
    restriction leftMap s = NodePuncturedDenominatorRestriction.left s :=
  restriction_comp first.toRingHom Polynomial.toLaurent s

/-- The right affine pullback uses the second faithful punctured restriction. -/
lemma right_eq (s : A (R := R)) :
    restriction rightMap s = NodePuncturedDenominatorRestriction.right s :=
  restriction_comp second.toRingHom Polynomial.toLaurent s

/-- Both concrete punctured pullback maps jointly detect equality. -/
lemma split_ext (s : A (R := R)) {a b : Localization.Away s}
    (hl : restriction leftMap s a = restriction leftMap s b)
    (hr : restriction rightMap s a = restriction rightMap s b) : a = b := by
  rw [left_eq] at hl
  rw [right_eq] at hr
  exact NodePuncturedDenominatorRestriction.split_ext s hl hr

variable {K : Type u} [Field K]

/-- The B-chart puncture pullback is the faithful one-gon restriction. -/
lemma one_eq (s : B (R := K)) :
    restriction bPunctureMap s = NodePuncturedDenominatorRestriction.one s :=
  restriction_comp (B (R := K)).val.toRingHom
    (algebraMap K[X] (NodePuncturedDenominatorRestriction.puncture K)) s

/-- The actual punctured B-chart pullback detects equality. -/
lemma one_injective (s : B (R := K)) :
    Function.Injective (restriction bPunctureMap s) := by
  rw [one_eq]
  exact NodePuncturedDenominatorRestriction.one_injective s

/-- Gamma of the first punctured pullback is its explicit ring restriction. -/
lemma left_appTop (s : A (R := R)) (z : Γ(Spec (.of (Localization.Away s)), ⊤)) :
    (Scheme.ΓSpecIso (.of (Localization.Away (leftMap s)))).hom
      ((Spec.map (CommRingCat.ofHom (restriction leftMap s))).appTop z) =
        NodePuncturedDenominatorRestriction.left s
          ((Scheme.ΓSpecIso (.of (Localization.Away s))).hom z) := by
  rw [PrincipalLocalizationPullback.restriction_appTop, left_eq]
  rfl

/-- Gamma of the second punctured pullback is its explicit ring restriction. -/
lemma right_appTop (s : A (R := R)) (z : Γ(Spec (.of (Localization.Away s)), ⊤)) :
    (Scheme.ΓSpecIso (.of (Localization.Away (rightMap s)))).hom
      ((Spec.map (CommRingCat.ofHom (restriction rightMap s))).appTop z) =
        NodePuncturedDenominatorRestriction.right s
          ((Scheme.ΓSpecIso (.of (Localization.Away s))).hom z) := by
  rw [PrincipalLocalizationPullback.restriction_appTop, right_eq]
  rfl

end FLT.Mazur.PuncturedNodeRestrictionComparison

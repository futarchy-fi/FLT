/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizationJointRestriction
public import FLT.Mazur.PolygonNodePresentation

/-!
# Restrictions from the actual localized node rings

For every denominator in A or B, restrictions land in the corresponding
localized normalization rings and detect equality. These statements apply to
the principal denominators chosen by the polygon charts without rescaling.
-/

@[expose] public noncomputable section
open scoped Polynomial

namespace FLT.Mazur.NodeDenominatorRestriction

open PolygonNodeEqualizer PolygonNodePresentation LocalizationJointRestriction
variable {R : Type*} [CommRing R]

/-- The first branch of an arbitrary principal split-node open. -/
def left (s : A (R := R)) :
    Localization.Away s →+* Localization.Away (first s) :=
  restriction first.toRingHom s

/-- The second branch uses the same node denominator. -/
def right (s : A (R := R)) :
    Localization.Away s →+* Localization.Away (second s) :=
  restriction second.toRingHom s

/-- Both branch restrictions together are faithful, including at the node. -/
lemma split_injective (s : A (R := R)) :
    Function.Injective ((left s).prod (right s)) := by
  apply joint_injective
  intro a ha hb
  exact Subtype.ext (Prod.ext ha hb)

/-- Equality on both localized branches is equality in the actual node ring. -/
lemma split_ext (s : A (R := R)) {a b : Localization.Away s}
    (hl : left s a = left s b) (hr : right s a = right s b) : a = b :=
  split_injective s (Prod.ext hl hr)

/-- Compute a ratio jointly, retaining both numerator polynomials. -/
lemma split_fraction (s a : A (R := R)) (n : ℕ) :
    (left s (algebraMap _ (Localization.Away s) a * IsLocalization.Away.invSelf s ^ n),
      right s (algebraMap _ (Localization.Away s) a * IsLocalization.Away.invSelf s ^ n)) =
    (algebraMap _ (Localization.Away (first s)) (first a) *
        IsLocalization.Away.invSelf (first s) ^ n,
      algebraMap _ (Localization.Away (second s)) (second a) *
        IsLocalization.Away.invSelf (second s) ^ n) :=
  Prod.ext (restriction_fraction first.toRingHom s a n)
    (restriction_fraction second.toRingHom s a n)

/-- The normalization restriction on the self-pinched node's principal open. -/
def one (s : B (R := R)) : Localization.Away s →+* Localization.Away s.val :=
  restriction (B (R := R)).val.toRingHom s

/-- The normalization detects equality on the actual localized one-gon ring. -/
lemma one_injective (s : B (R := R)) : Function.Injective (one s) :=
  restriction_injective _ s Subtype.val_injective

/-- One-gon fractions retain the complete numerator, including self-incidence terms. -/
lemma one_fraction (s a : B (R := R)) (n : ℕ) :
    one s (algebraMap _ (Localization.Away s) a * IsLocalization.Away.invSelf s ^ n) =
      algebraMap _ (Localization.Away s.val) a.val *
        IsLocalization.Away.invSelf s.val ^ n :=
  restriction_fraction _ s a n

end FLT.Mazur.NodeDenominatorRestriction

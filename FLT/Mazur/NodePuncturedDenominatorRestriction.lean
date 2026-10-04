/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodeDenominatorRestriction

/-!
# Detecting node functions on the punctured normalization

The split branches can be further restricted to their Laurent opens without
losing equality detection. For the one-gon, invert the conductor to remove
both identified endpoints. This allows ring calculations away from the node
to determine functions in the actual localized node ring.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Polynomial LaurentPolynomial

namespace FLT.Mazur.NodePuncturedDenominatorRestriction

open PolygonNodeEqualizer PolygonNodePresentation LocalizationJointRestriction
variable {R : Type*} [CommRing R]

/-- First branch restriction with its branch coordinate also inverted. -/
def left (s : A (R := R)) :
    Localization.Away s →+* Localization.Away (first s).toLaurent :=
  (restriction (Polynomial.toLaurent : R[X] →+* R[T;T⁻¹]) (first s)).comp
    (NodeDenominatorRestriction.left s)

/-- Second branch restriction with its own coordinate inverted. -/
def right (s : A (R := R)) :
    Localization.Away s →+* Localization.Away (second s).toLaurent :=
  (restriction (Polynomial.toLaurent : R[X] →+* R[T;T⁻¹]) (second s)).comp
    (NodeDenominatorRestriction.right s)

/-- Equality on both punctured refinements determines the original node function. -/
lemma split_ext (s : A (R := R)) {a b : Localization.Away s}
    (hl : left s a = left s b) (hr : right s a = right s b) : a = b := by
  apply NodeDenominatorRestriction.split_ext s
  · exact restriction_injective (Polynomial.toLaurent : R[X] →+* R[T;T⁻¹]) (first s)
      Polynomial.toLaurent_injective hl
  · exact restriction_injective (Polynomial.toLaurent : R[X] →+* R[T;T⁻¹]) (second s)
      Polynomial.toLaurent_injective hr

variable {K : Type*} [Field K]

/-- Localizing a polynomial domain at a nonzero polynomial is faithful. -/
lemma polynomial_localization_injective (s : K[X]) (hs : s ≠ 0) :
    Function.Injective (algebraMap K[X] (Localization.Away s)) := by
  intro a b hab
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq s hab
  exact mul_left_cancel₀ (pow_ne_zero n hs) hn

/-- The normalization ring after deleting both one-gon endpoints. -/
abbrev puncture (K : Type*) [Field K] :=
  Localization.Away (Polynomial.X * (Polynomial.X - 1) : K[X])

/-- Restriction to the conductor open is faithful before any further refinement. -/
lemma puncture_injective : Function.Injective (algebraMap K[X] (puncture K)) := by
  apply polynomial_localization_injective
  exact mul_ne_zero Polynomial.X_ne_zero (by simpa using Polynomial.X_sub_C_ne_zero (1 : K))

/-- Restrict the actual B_f ring to the normalization with both endpoints removed. -/
def one (s : B (R := K)) :
    Localization.Away s →+* Localization.Away (algebraMap K[X] (puncture K) s.val) :=
  (restriction (algebraMap K[X] (puncture K)) s.val).comp (NodeDenominatorRestriction.one s)

/-- Punctured normalization computations still determine the self-pinched node function. -/
lemma one_injective (s : B (R := K)) : Function.Injective (one s) :=
  (restriction_injective _ _ puncture_injective).comp (NodeDenominatorRestriction.one_injective s)

end FLT.Mazur.NodePuncturedDenominatorRestriction

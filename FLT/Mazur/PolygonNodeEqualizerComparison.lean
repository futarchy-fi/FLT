/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonDenominatorEqualizer
public import FLT.Mazur.PolygonNodeRingComparison

/-!
# Exact equalizer rings on the polygon's chosen node opens

The principal denominators have nonzero node values because their basic opens
contain the specified origins. Thus the unnormalized equalizer descriptions
apply directly to the actual affine section rings in the cover.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.PolygonNodeAffineCharts

open PolygonPinching PolygonNodePresentation
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ) (hn₂ : 2 ≤ n) (i : Fin n) (x : Spec (.of K))

/-- The selected denominator has a nonzero value at the actual split node. -/
lemma splitDenominator_value_ne_zero : aEval (splitDenominator K n hn p q h a hn₂ i x) ≠ 0 := by
  have hm := splitDenominator_origin_mem K n hn p q h a hn₂ i x
  change aEval (splitDenominator K n hn p q h a hn₂ i x) ∉ x.asIdeal at hm
  intro hz
  exact hm (hz ▸ x.asIdeal.zero_mem)

/-- Its value is therefore a unit, without rescaling the denominator. -/
lemma splitDenominator_value_isUnit :
    IsUnit (aEval (splitDenominator K n hn p q h a hn₂ i x)) :=
  isUnit_iff_ne_zero.mpr (splitDenominator_value_ne_zero K n hn p q h a hn₂ i x)

/-- Actual sections identify with matching localized branch functions. -/
def splitEqualizerEquiv :
    Γ(C.left, splitDenominatorChart K n hn p q h a hn₂ i x ''ᵁ ⊤) ≃+*
      NodeDenominatorEqualizer.E (splitDenominator K n hn p q h a hn₂ i x)
        (splitDenominator_value_isUnit K n hn p q h a hn₂ i x) :=
  (splitDenominatorSectionsIso K n hn p q h a hn₂ i x).commRingCatIsoToRingEquiv.trans
    (NodeDenominatorEqualizer.equiv _ _)

/-- The equalizer comparison preserves both previously specified restrictions. -/
lemma splitEqualizerEquiv_val
    (z : Γ(C.left, splitDenominatorChart K n hn p q h a hn₂ i x ''ᵁ ⊤)) :
    (splitEqualizerEquiv K n hn p q h a hn₂ i x z).val =
      (splitLeftRestriction K n hn p q h a hn₂ i x z,
        splitRightRestriction K n hn p q h a hn₂ i x z) :=
  RingHom.congr_fun (NodeDenominatorEqualizer.equiv_branches _ _)
    ((splitDenominatorSectionsIso K n hn p q h a hn₂ i x).hom z)

end PolygonNodeAffineCharts

namespace PolygonNodeAffineCharts
open PolygonPinching PolygonNodePresentation
variable (K : Type u) [Field K] (hn : 0 < 1)
  {C : Over (Spec (.of K))} (p : components K 1 ⟶ C) (q : nodes K 1 ⟶ C)
  (h : IsPushout (toComponents K 1 hn) (toNodes K 1) p q)
  (a : Fin 1 → Kˣ) (x : Spec (.of K))

/-- The one-gon denominator is nonzero at the identified endpoints. -/
lemma oneDenominator_value_ne_zero : bEval (oneDenominator K hn p q h a x) ≠ 0 := by
  have hm := oneDenominator_origin_mem K hn p q h a x
  change bEval (oneDenominator K hn p q h a x) ∉ x.asIdeal at hm
  intro hz
  exact hm (hz ▸ x.asIdeal.zero_mem)

/-- The same denominator, with no normalization, has a unit endpoint value. -/
lemma oneDenominator_value_isUnit : IsUnit (bEval (oneDenominator K hn p q h a x)) :=
  isUnit_iff_ne_zero.mpr (oneDenominator_value_ne_zero K hn p q h a x)

/-- Actual one-gon sections are exactly the localized functions with equal endpoint values. -/
def oneEqualizerEquiv : Γ(C.left, oneDenominatorChart K hn p q h a x ''ᵁ ⊤) ≃+*
    OneGonDenominatorEqualizer.E (oneDenominator K hn p q h a x)
      (oneDenominator_value_isUnit K hn p q h a x) :=
  (oneDenominatorSectionsIso K hn p q h a x).commRingCatIsoToRingEquiv.trans
    (OneGonDenominatorEqualizer.equiv _ _)

/-- The one-gon equalizer comparison preserves the actual normalization restriction. -/
lemma oneEqualizerEquiv_val (z : Γ(C.left, oneDenominatorChart K hn p q h a x ''ᵁ ⊤)) :
    (oneEqualizerEquiv K hn p q h a x z).val = oneRestriction K hn p q h a x z :=
  RingHom.congr_fun (OneGonDenominatorEqualizer.equiv_restriction _ _)
    ((oneDenominatorSectionsIso K hn p q h a x).hom z)

end FLT.Mazur.PolygonNodeAffineCharts

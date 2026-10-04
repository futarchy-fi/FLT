/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodeDenominatorRestriction
public import FLT.Mazur.PolygonNodeDenominatorCover
public import FLT.Mazur.PrincipalLocalizationPullback

/-!
# Ring comparisons on the specified polygon node opens

Use the exact denominators selected by the node cover. Gamma of each actual
image is its localized node ring; normalization restriction is computed by
the corresponding localized ring homomorphism. Both split branches are kept
for every node index, including both indices of a two-gon.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace FLT.Mazur.PolygonNodeAffineCharts

open PolygonPinching PolygonNodeEqualizer PolygonNodePresentation
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ) (hn₂ : 2 ≤ n) (i : Fin n) (x : Spec (.of K))

/-- Restriction of actual node-open sections to the first localized branch ring. -/
def splitLeftRestriction :
    Γ(C.left, splitDenominatorChart K n hn p q h a hn₂ i x ''ᵁ ⊤) →+*
      Localization.Away (first (splitDenominator K n hn p q h a hn₂ i x)) :=
  (NodeDenominatorRestriction.left _).comp
    (splitDenominatorSectionsIso K n hn p q h a hn₂ i x).hom.hom

/-- Restriction of the same sections to the second localized branch ring. -/
def splitRightRestriction :
    Γ(C.left, splitDenominatorChart K n hn p q h a hn₂ i x ''ᵁ ⊤) →+*
      Localization.Away (second (splitDenominator K n hn p q h a hn₂ i x)) :=
  (NodeDenominatorRestriction.right _).comp
    (splitDenominatorSectionsIso K n hn p q h a hn₂ i x).hom.hom

/-- Joint branch computations uniquely determine a section on the actual node open. -/
lemma split_sections_ext
    {r t : Γ(C.left, splitDenominatorChart K n hn p q h a hn₂ i x ''ᵁ ⊤)}
    (hl : splitLeftRestriction K n hn p q h a hn₂ i x r =
      splitLeftRestriction K n hn p q h a hn₂ i x t)
    (hr : splitRightRestriction K n hn p q h a hn₂ i x r =
      splitRightRestriction K n hn p q h a hn₂ i x t) : r = t := by
  apply (splitDenominatorSectionsIso K n hn p q h a hn₂ i x).commRingCatIsoToRingEquiv.injective
  exact NodeDenominatorRestriction.split_ext _ hl hr

/-- The first normalization refinement is the actual pullback of the node localization. -/
lemma split_left_isPullback :
    let s := splitDenominator K n hn p q h a hn₂ i x
    IsPullback (PrincipalAffineRefinement.inclusion (first s))
      (Spec.map (CommRingCat.ofHom (NodeDenominatorRestriction.left s)))
      (Spec.map (CommRingCat.ofHom (first (R := K)).toRingHom))
      (PrincipalAffineRefinement.inclusion s) :=
  PrincipalLocalizationPullback.isPullback (first (R := K)).toRingHom
    (splitDenominator K n hn p q h a hn₂ i x)

/-- The second normalization refinement uses the same chosen node localization. -/
lemma split_right_isPullback :
    let s := splitDenominator K n hn p q h a hn₂ i x
    IsPullback (PrincipalAffineRefinement.inclusion (second s))
      (Spec.map (CommRingCat.ofHom (NodeDenominatorRestriction.right s)))
      (Spec.map (CommRingCat.ofHom (second (R := K)).toRingHom))
      (PrincipalAffineRefinement.inclusion s) :=
  PrincipalLocalizationPullback.isPullback (second (R := K)).toRingHom
    (splitDenominator K n hn p q h a hn₂ i x)

/-- The first ring restriction is the structure-sheaf pullback on the refinement. -/
lemma splitLeftRestriction_eq_appTop
    (z : Γ(C.left, splitDenominatorChart K n hn p q h a hn₂ i x ''ᵁ ⊤)) :
    let s := splitDenominator K n hn p q h a hn₂ i x
    splitLeftRestriction K n hn p q h a hn₂ i x z =
      (Scheme.ΓSpecIso (.of (Localization.Away (first s)))).hom
        ((Spec.map (CommRingCat.ofHom (NodeDenominatorRestriction.left s))).appTop
          ((splitDenominatorChart K n hn p q h a hn₂ i x).appIso ⊤ |>.hom <| z)) :=
  (PrincipalLocalizationPullback.restriction_appTop _ _ _).symm

/-- The second ring restriction is likewise the actual sheaf pullback. -/
lemma splitRightRestriction_eq_appTop
    (z : Γ(C.left, splitDenominatorChart K n hn p q h a hn₂ i x ''ᵁ ⊤)) :
    let s := splitDenominator K n hn p q h a hn₂ i x
    splitRightRestriction K n hn p q h a hn₂ i x z =
      (Scheme.ΓSpecIso (.of (Localization.Away (second s)))).hom
        ((Spec.map (CommRingCat.ofHom (NodeDenominatorRestriction.right s))).appTop
          ((splitDenominatorChart K n hn p q h a hn₂ i x).appIso ⊤ |>.hom <| z)) :=
  (PrincipalLocalizationPullback.restriction_appTop _ _ _).symm

end PolygonNodeAffineCharts

namespace PolygonNodeAffineCharts
open PolygonPinching PolygonNodePresentation
variable (K : Type u) [Field K] (hn : 0 < 1)
  {C : Over (Spec (.of K))} (p : components K 1 ⟶ C) (q : nodes K 1 ⟶ C)
  (h : IsPushout (toComponents K 1 hn) (toNodes K 1) p q)
  (a : Fin 1 → Kˣ) (x : Spec (.of K))

/-- The one-gon uses its actual equal-endpoint ring, with no split-node substitution. -/
def oneRestriction : Γ(C.left, oneDenominatorChart K hn p q h a x ''ᵁ ⊤) →+*
    Localization.Away (oneDenominator K hn p q h a x).val :=
  (NodeDenominatorRestriction.one _).comp
    (oneDenominatorSectionsIso K hn p q h a x).hom.hom

/-- Normalization detects sections on the actual one-gon denominator open. -/
lemma oneRestriction_injective : Function.Injective (oneRestriction K hn p q h a x) :=
  (NodeDenominatorRestriction.one_injective _).comp
    (oneDenominatorSectionsIso K hn p q h a x).commRingCatIsoToRingEquiv.injective

/-- The one-gon normalization refinement is the pullback along B into K[X]. -/
lemma one_isPullback :
    let s := oneDenominator K hn p q h a x
    IsPullback (PrincipalAffineRefinement.inclusion s.val)
      (Spec.map (CommRingCat.ofHom (NodeDenominatorRestriction.one s)))
      (Spec.map (CommRingCat.ofHom (B (R := K)).val.toRingHom))
      (PrincipalAffineRefinement.inclusion s) :=
  PrincipalLocalizationPullback.isPullback (B (R := K)).val.toRingHom
    (oneDenominator K hn p q h a x)

/-- The one-gon ring restriction computes the actual structure-sheaf pullback. -/
lemma oneRestriction_eq_appTop
    (z : Γ(C.left, oneDenominatorChart K hn p q h a x ''ᵁ ⊤)) :
    let s := oneDenominator K hn p q h a x
    oneRestriction K hn p q h a x z =
      (Scheme.ΓSpecIso (.of (Localization.Away s.val))).hom
        ((Spec.map (CommRingCat.ofHom (NodeDenominatorRestriction.one s))).appTop
          ((oneDenominatorChart K hn p q h a x).appIso ⊤ |>.hom <| z)) :=
  (PrincipalLocalizationPullback.restriction_appTop _ _ _).symm

end FLT.Mazur.PolygonNodeAffineCharts

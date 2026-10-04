/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodeRingComparison
public import FLT.Mazur.PolygonSplitTorusBranches
public import FLT.Mazur.PrincipalLocalizationIntersection

/-!
# The actual split-node and torus intersections

The affine coordinate rings are the Laurent localizations of the two branch
denominators. The right square includes inversion and the cyclic successor;
no index is discarded for a two-gon.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonNodeAffineCharts
open PolygonPinching PolygonNodeEqualizer PolygonNodeLocalization
open PrincipalAffineRefinement LocalizationJointRestriction
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ) (hn₂ : 2 ≤ n) (i : Fin n) (x : Spec (.of K))

/-- The punctured first branch is the pullback along the actual i-th torus. -/
lemma split_left_punctured_isPullback :
    let s := splitDenominator K n hn p q h a hn₂ i x
    IsPullback (Spec.map (CommRingCat.ofHom (restriction leftMap s)))
      (inclusion (first s).toLaurent)
      (splitDenominatorChart K n hn p q h a hn₂ i x)
      (torusToComponent K ≫ componentι K n i ≫ p).left := by
  dsimp only
  rw [← left_splitChart K n hn p q h hn₂ i]
  exact PrincipalLocalizationIntersection.isPullback leftMap _ _

/-- The right puncture uses the inverted coordinate of the next component. -/
lemma split_right_punctured_isPullback :
    let s := splitDenominator K n hn p q h a hn₂ i x
    IsPullback (Spec.map (CommRingCat.ofHom (restriction rightMap s)))
      (inclusion (second s).toLaurent)
      (splitDenominatorChart K n hn p q h a hn₂ i x)
      ((ProjectiveLine.inversion K).inv ≫
        (torusToComponent K ≫ componentι K n (finRotate n i) ≫ p).left) := by
  dsimp only
  rw [← right_splitChart K n hn p q h hn₂ i]
  exact PrincipalLocalizationIntersection.isPullback rightMap _ _

/-- Sections on the intersection with component i have its punctured branch ring. -/
def splitLeftIntersectionSectionsIso :
    let := torus_isOpenImmersion K n hn p q h i
    let s := splitDenominator K n hn p q h a hn₂ i x
    Γ(C.left, (splitDenominatorChart K n hn p q h a hn₂ i x ''ᵁ ⊤) ⊓
      ((torusToComponent K ≫ componentι K n i ≫ p).left ''ᵁ ⊤)) ≅
      CommRingCat.of (Localization.Away (first s).toLaurent) := by
  let := torus_isOpenImmersion K n hn p q h i
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (leftMap (R := K)))) :=
    PolygonNodeBranches.left_isOpenImmersion K
  have e := PrincipalLocalizationIntersection.sectionsIso (leftMap (R := K))
    (splitDenominator K n hn p q h a hn₂ i x) (splitChart K n hn p q h hn₂ i)
  change Γ(C.left, (splitDenominatorChart K n hn p q h a hn₂ i x ''ᵁ ⊤) ⊓
    ((PolygonNodeBranches.left K ≫ splitChart K n hn p q h hn₂ i) ''ᵁ ⊤)) ≅ _ at e
  simpa only [left_splitChart, leftMap_apply] using e

/-- Sections on the successor intersection have the second punctured branch ring. -/
def splitRightIntersectionSectionsIso :
    let := torus_isOpenImmersion K n hn p q h (finRotate n i)
    let s := splitDenominator K n hn p q h a hn₂ i x
    Γ(C.left, (splitDenominatorChart K n hn p q h a hn₂ i x ''ᵁ ⊤) ⊓
      ((torusToComponent K ≫ componentι K n (finRotate n i) ≫ p).left ''ᵁ ⊤)) ≅
      CommRingCat.of (Localization.Away (second s).toLaurent) := by
  let := torus_isOpenImmersion K n hn p q h (finRotate n i)
  have he : (PolygonNodeBranches.right K ≫ splitChart K n hn p q h hn₂ i) ''ᵁ ⊤ =
      (torusToComponent K ≫ componentι K n (finRotate n i) ≫ p).left ''ᵁ ⊤ := by
    simp only [right_splitChart, Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.opensRange_comp_of_isIso]
  dsimp only
  rw [← he]
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (rightMap (R := K)))) :=
    PolygonNodeBranches.right_isOpenImmersion K
  exact PrincipalLocalizationIntersection.sectionsIso rightMap _ _

/-- With the original successor torus coordinate, inversion is in the ring map. -/
lemma split_right_punctured_spec_isPullback :
    let s := splitDenominator K n hn p q h a hn₂ i x
    IsPullback (Spec.map (CommRingCat.ofHom (restriction rightMap s)))
      (Spec.map (CommRingCat.ofHom
        ((algebraMap (LaurentPolynomial K) (Localization.Away (second s).toLaurent)).comp
          (LaurentPolynomial.invert (R := K)).toRingHom)))
      (splitDenominatorChart K n hn p q h a hn₂ i x)
      (torusToComponent K ≫ componentι K n (finRotate n i) ≫ p).left := by
  dsimp only
  let t := (torusToComponent K ≫ componentι K n (finRotate n i) ≫ p).left
  have hb : IsPullback ((ProjectiveLine.inversion K).inv ≫ t)
      (ProjectiveLine.inversion K).inv (𝟙 _) t :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have he := (split_right_punctured_isPullback K n hn p q h a hn₂ i x).paste_vert hb
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  change IsPullback _
    (inclusion (second (splitDenominator K n hn p q h a hn₂ i x)).toLaurent ≫
      (ProjectiveLine.inversion K).inv) _ t
  simpa only [Category.comp_id] using he

end FLT.Mazur.PolygonNodeAffineCharts

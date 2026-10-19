/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductTestUniqueness

/-!
# Recovery by restrictions of constructed local parameters

Further restriction of a constructed affine parameter recovers the prescribed
original comparison on the composite test. A separately named composite map
allows two overlap projections to be compared with identical endpoints.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool) {T V : Scheme}
  (q : T ⟶ normalizedLocus n b) (r : T ⟶ normalizedLocus n c)
  (e : (normalizedCurve n b).baseChange q ≅ (normalizedCurve n c).baseChange r)
local notation "s" => productComparisonStructure n b c
local notation "p" => prod.lift q r
local notation "C" => AffineMorphismTestCover.cover p
local notation "U" i => AffineMorphismTestCover.targetOpen p i
local notation "t" i => AffineMorphismTestCover.toSpectrum p i
local notation "L" i => productOpenLeft n b c (U i)
local notation "R" i => productOpenRight n b c (U i)

/-- A restricted local parameter lies over the specified composite original test. -/
theorem productLocalRestriction_base (i : (C).I₀) (l : V ⟶ (C).X i)
    (v : V ⟶ T) (hv : l ≫ (C).f i = v) :
    (l ≫ productLocalParameter n b c q r e i) ≫ s = prod.lift (v ≫ q) (v ≫ r) := by
  rw [Category.assoc, productLocalParameter_base, ← Category.assoc, hv]
  apply prod.hom_ext <;> simp only [Category.assoc, prod.lift_fst, prod.lift_snd]

/-- A restricted local parameter recovers the direct original-family comparison. -/
theorem productLocalRestriction_recovers (i : (C).I₀) (l : V ⟶ (C).X i)
    (v : V ⟶ T) (hv : l ≫ (C).f i = v) :
    productUniversalComparisonOnTest n b c (l ≫ productLocalParameter n b c q r e i)
        (v ≫ q) (v ≫ r)
        (productPairTest_left n b c (v ≫ q) (v ≫ r) _
          (productLocalRestriction_base n b c q r e i l v hv))
        (productPairTest_right n b c (v ≫ q) (v ≫ r) _
          (productLocalRestriction_base n b c q r e i l v hv)) =
      comparisonPullbackBetween (normalizedCurve n b) (normalizedCurve n c)
        q r v (v ≫ q) (v ≫ r) rfl rfl e := by
  subst v
  have hq : (l ≫ (C).f i) ≫ q = l ≫ ((t i) ≫ (L i)) := by
    rw [productLocalTest_left, Category.assoc]
  have hr : (l ≫ (C).f i) ≫ r = l ≫ ((t i) ≫ (R i)) := by
    rw [productLocalTest_right, Category.assoc]
  let k := (productLocalParameter_existsUnique n b c q r e i).choose
  have hk := productLocalParameter_recovers n b c q r e i
  change productUniversalComparisonOnTest n b c k.val ((t i) ≫ (L i))
    ((t i) ≫ (R i)) _ _ = productLocalTestComparison n b c q r e i at hk
  have h := productUniversalComparisonOnTest_restrict n b c l ((t i) ≫ (L i))
    ((t i) ≫ (R i)) ((l ≫ (C).f i) ≫ q) ((l ≫ (C).f i) ≫ r) hq hr k.val
    (productSpectrumTest_left n b c (U i) (t i) k)
    (productSpectrumTest_right n b c (U i) (t i) k)
  rw [hk] at h
  refine h.symm.trans ?_
  exact comparisonPullbackBetween_restrict (normalizedCurve n b) (normalizedCurve n c)
    q r ((C).f i) l ((l ≫ (C).f i) ≫ q) ((l ≫ (C).f i) ≫ r)
    ((t i) ≫ (L i)) ((t i) ≫ (R i)) (productLocalTest_left n b c q r i)
    (productLocalTest_right n b c q r i) hq hr e

end FLT.Mazur.CyclicCharacteristicAtlas

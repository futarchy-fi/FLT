/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductLocalRestriction
public import FLT.Mazur.GeneralizedCurveCoverMorphism

/-!
# Full original-family classification on arbitrary scheme tests

The actual affine parameters agree on overlaps by full comparison uniqueness.
They glue to a parameter recovering the prescribed comparison, and the same
uniqueness theorem shows that this global parameter is unique.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool) {T : Scheme}
  (q : T ⟶ normalizedLocus n b) (r : T ⟶ normalizedLocus n c)
  (e : (normalizedCurve n b).baseChange q ≅ (normalizedCurve n c).baseChange r)
local notation "s" => productComparisonStructure n b c
local notation "p" => prod.lift q r
local notation "C" => AffineMorphismTestCover.cover p
local notation "U" i => AffineMorphismTestCover.targetOpen p i
local notation "t" i => AffineMorphismTestCover.toSpectrum p i
local notation "L" i => productOpenLeft n b c (U i)
local notation "R" i => productOpenRight n b c (U i)

/-- Constructed affine parameters agree on actual overlaps; compatibility is proved. -/
theorem productLocalParameter_overlap (i j : (C).I₀) :
    pullback.fst ((C).f i) ((C).f j) ≫ productLocalParameter n b c q r e i =
      pullback.snd ((C).f i) ((C).f j) ≫ productLocalParameter n b c q r e j := by
  let l := pullback.fst ((C).f i) ((C).f j)
  let m := pullback.snd ((C).f i) ((C).f j)
  let v := l ≫ (C).f i
  have hm : m ≫ (C).f j = v := pullback.condition.symm
  exact productRecoveringParameter_unique n b c (v ≫ q) (v ≫ r)
    (comparisonPullbackBetween (normalizedCurve n b) (normalizedCurve n c)
      q r v (v ≫ q) (v ≫ r) rfl rfl e)
    (l ≫ productLocalParameter n b c q r e i) (m ≫ productLocalParameter n b c q r e j)
    (productLocalRestriction_base n b c q r e i l v rfl)
    (productLocalRestriction_base n b c q r e j m v hm)
    (productLocalRestriction_recovers n b c q r e i l v rfl)
    (productLocalRestriction_recovers n b c q r e j m v hm)

/-- Glue the actual constructed local maps to the full comparison parameter scheme. -/
def productComparisonParameter : T ⟶ productComparisonScheme n b c :=
  (C).glueMorphisms (productLocalParameter n b c q r e)
    (productLocalParameter_overlap n b c q r e)

/-- The global parameter restricts to each constructed affine parameter. -/
theorem productComparisonParameter_local (i : (C).I₀) :
    (C).f i ≫ productComparisonParameter n b c q r e =
      productLocalParameter n b c q r e i :=
  (C).ι_glueMorphisms _ _ i

/-- The global parameter retains the prescribed ordered pair of original base maps. -/
theorem productComparisonParameter_base :
    productComparisonParameter n b c q r e ≫ s = p := by
  apply (C).hom_ext
  intro i
  rw [← Category.assoc, productComparisonParameter_local, productLocalParameter_base]

/-- The glued parameter recovers the entire prescribed original-family comparison. -/
theorem productComparisonParameter_recovers :
    productUniversalComparisonOnTest n b c (productComparisonParameter n b c q r e) q r
        (productPairTest_left n b c q r _ (productComparisonParameter_base n b c q r e))
        (productPairTest_right n b c q r _ (productComparisonParameter_base n b c q r e)) =
      e := by
  let f := productComparisonParameter n b c q r e
  let a := productUniversalComparisonOnTest n b c f q r
    (productPairTest_left n b c q r f (productComparisonParameter_base n b c q r e))
    (productPairTest_right n b c q r f (productComparisonParameter_base n b c q r e))
  change a = e
  apply Iso.ext
  apply hom_ext_of_cover (C)
  intro i
  let A := (normalizedCurve n b).baseChangeCompEqIso q ((C).f i) ((t i) ≫ (L i))
    (productLocalTest_left n b c q r i)
  let B := (normalizedCurve n c).baseChangeCompEqIso r ((C).f i) ((t i) ≫ (R i))
    (productLocalTest_right n b c q r i)
  have h := productUniversalComparisonOnTest_restrict n b c ((C).f i) q r
    ((t i) ≫ (L i)) ((t i) ≫ (R i)) (productLocalTest_left n b c q r i)
    (productLocalTest_right n b c q r i) f
    (productPairTest_left n b c q r f (productComparisonParameter_base n b c q r e))
    (productPairTest_right n b c q r f (productComparisonParameter_base n b c q r e))
  have hf : (C).f i ≫ f = productLocalParameter n b c q r e i :=
    productComparisonParameter_local n b c q r e i
  simp only [hf] at h
  have hk := productLocalParameter_recovers n b c q r e i
  change productUniversalComparisonOnTest n b c (productLocalParameter n b c q r e i)
    ((t i) ≫ (L i)) ((t i) ≫ (R i)) _ _ = _ at hk
  have h' := congrArg Iso.hom (h.trans hk)
  change A.hom ≫ baseChangeMap ((C).f i) a.hom ≫ B.inv =
    A.hom ≫ baseChangeMap ((C).f i) e.hom ≫ B.inv at h'
  exact (cancel_mono B.inv).mp ((cancel_epi A.hom).mp h')

/-- Every full original-family comparison on every scheme test has exactly one parameter. -/
theorem productComparisonParameter_existsUnique :
    ∃! k : {k : T ⟶ productComparisonScheme n b c // k ≫ s = p},
      productUniversalComparisonOnTest n b c k.val q r
        (productPairTest_left n b c q r k.val k.property)
        (productPairTest_right n b c q r k.val k.property) = e := by
  refine ⟨⟨productComparisonParameter n b c q r e,
    productComparisonParameter_base n b c q r e⟩,
    productComparisonParameter_recovers n b c q r e, ?_⟩
  intro k hk
  apply Subtype.ext
  exact productRecoveringParameter_unique n b c q r e k.val
    (productComparisonParameter n b c q r e) k.property
    (productComparisonParameter_base n b c q r e) hk
    (productComparisonParameter_recovers n b c q r e)

end FLT.Mazur.CyclicCharacteristicAtlas

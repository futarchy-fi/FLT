/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductLocalParameters

/-!
# Uniqueness of full comparison parameters on arbitrary scheme tests

A parameter recovering a prescribed original-family comparison restricts to
its constructed affine local parameters. The actual open cover then detects
equality of global parameter maps, without assuming affine test schemes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool) {T : Scheme}
  (q : T ⟶ normalizedLocus n b) (r : T ⟶ normalizedLocus n c)
local notation "s" => productComparisonStructure n b c
local notation "p" => prod.lift q r
local notation "C" => AffineMorphismTestCover.cover p
local notation "U" i => AffineMorphismTestCover.targetOpen p i
local notation "t" i => AffineMorphismTestCover.toSpectrum p i
local notation "L" i => productOpenLeft n b c (U i)
local notation "R" i => productOpenRight n b c (U i)

/-- The left endpoint of a parameter over the given ordered pair is its given base map. -/
theorem productPairTest_left (f : T ⟶ productComparisonScheme n b c) (hf : f ≫ s = p) :
    q = f ≫ (s ≫ prod.fst) := by rw [← Category.assoc, hf, prod.lift_fst]

/-- The right endpoint of a parameter over the given ordered pair is its given base map. -/
theorem productPairTest_right (f : T ⟶ productComparisonScheme n b c) (hf : f ≫ s = p) :
    r = f ≫ (s ≫ prod.snd) := by rw [← Category.assoc, hf, prod.lift_snd]

variable (e : (normalizedCurve n b).baseChange q ≅ (normalizedCurve n c).baseChange r)

/-- Any recovering global parameter restricts to the local parameter constructed from the curve. -/
theorem productRecoveringParameter_local
    (f : T ⟶ productComparisonScheme n b c) (hf : f ≫ s = p)
    (he : productUniversalComparisonOnTest n b c f q r
      (productPairTest_left n b c q r f hf) (productPairTest_right n b c q r f hf) = e)
    (i : (C).I₀) :
    (C).f i ≫ f = productLocalParameter n b c q r e i := by
  let k : {k : (C).X i ⟶ productComparisonScheme n b c //
      k ≫ s = ((t i) ≫ (U i).1.toScheme.isoSpec.inv) ≫ (U i).1.ι} :=
    ⟨(C).f i ≫ f, by rw [Category.assoc, hf, AffineMorphismTestCover.toSpectrum_base]⟩
  have hk : productSpectrumTestComparison n b c (U i) (t i) k =
      productLocalTestComparison n b c q r e i := by
    have h := productUniversalComparisonOnTest_restrict n b c ((C).f i) q r
      ((t i) ≫ (L i)) ((t i) ≫ (R i)) (productLocalTest_left n b c q r i)
      (productLocalTest_right n b c q r i) f (productPairTest_left n b c q r f hf)
      (productPairTest_right n b c q r f hf)
    rw [he] at h
    exact h.symm
  exact congrArg Subtype.val
    ((productLocalParameter_existsUnique n b c q r e i).choose_spec.2 k hk)

/-- Full original-family comparisons determine their parameter map on every scheme test. -/
theorem productRecoveringParameter_unique
    (f g : T ⟶ productComparisonScheme n b c) (hf : f ≫ s = p) (hg : g ≫ s = p)
    (he : productUniversalComparisonOnTest n b c f q r
      (productPairTest_left n b c q r f hf) (productPairTest_right n b c q r f hf) = e)
    (he' : productUniversalComparisonOnTest n b c g q r
      (productPairTest_left n b c q r g hg) (productPairTest_right n b c q r g hg) = e) :
    f = g := by
  apply (C).hom_ext
  intro i
  exact (productRecoveringParameter_local n b c q r e f hf he i).trans
    (productRecoveringParameter_local n b c q r e g hg he' i).symm

end FLT.Mazur.CyclicCharacteristicAtlas

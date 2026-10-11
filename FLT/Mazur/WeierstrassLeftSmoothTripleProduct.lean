/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothTripleProduct
public import FLT.Mazur.WeierstrassLeftSmoothFactorAddition

/-!
# Two smooth inputs and an arbitrary third input

The actual fiber product retains the three original points. Both iterated sums
are constructed using coefficient compatibility; associativity remains a theorem
to prove, not a field assumed in this construction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The actual product of two smooth copies and the whole original cubic. -/
abbrev leftSmoothTriple :=
  pullback (smoothFactorProductStructure W) (integralCurveStructure W)

/-- Projection to the first pair. -/
abbrev leftSmoothTriplePair : leftSmoothTriple W ⟶ smoothFactorProduct W :=
  pullback.fst _ _

/-- First input of the actual triple product. -/
def leftSmoothTripleFirst : leftSmoothTriple W ⟶ (integralSmoothOpen W).toScheme :=
  leftSmoothTriplePair W ≫ pullback.fst _ _

/-- Second input of the actual triple product. -/
def leftSmoothTripleSecond : leftSmoothTriple W ⟶ (integralSmoothOpen W).toScheme :=
  leftSmoothTriplePair W ≫ pullback.snd _ _

/-- The unrestricted third input of the actual triple product. -/
abbrev leftSmoothTripleThird : leftSmoothTriple W ⟶ integralCurve W :=
  pullback.snd _ _

/-- The first two inputs have the same coefficient map. -/
theorem leftSmoothTriple_first_second :
    leftSmoothTripleFirst W ≫ integralSmoothStructure W =
      leftSmoothTripleSecond W ≫ integralSmoothStructure W := by
  simp only [leftSmoothTripleFirst, leftSmoothTripleSecond, Category.assoc]
  exact congrArg (fun f => leftSmoothTriplePair W ≫ f) pullback.condition

/-- The first and third inputs have the same coefficient map. -/
theorem leftSmoothTriple_first_third :
    leftSmoothTripleFirst W ≫ integralSmoothStructure W =
      leftSmoothTripleThird W ≫ integralCurveStructure W := by
  exact (Category.assoc _ _ _).trans pullback.condition

/-- The second and third inputs have the same coefficient map. -/
theorem leftSmoothTriple_second_third :
    leftSmoothTripleSecond W ≫ integralSmoothStructure W =
      leftSmoothTripleThird W ≫ integralCurveStructure W :=
  (leftSmoothTriple_first_second W).symm.trans (leftSmoothTriple_first_third W)

/-- Projection to the last pair. -/
def leftSmoothTripleLastPair : leftSmoothTriple W ⟶ leftSmoothFactorProduct W :=
  pullback.lift (leftSmoothTripleSecond W) (leftSmoothTripleThird W)
    (leftSmoothTriple_second_third W)

/-- First projection of the last pair. -/
@[reassoc (attr := simp)] theorem leftSmoothTripleLastPair_fst :
    leftSmoothTripleLastPair W ≫ pullback.fst _ _ = leftSmoothTripleSecond W :=
  pullback.lift_fst _ _ _

/-- Second projection of the last pair. -/
@[reassoc (attr := simp)] theorem leftSmoothTripleLastPair_snd :
    leftSmoothTripleLastPair W ≫ pullback.snd _ _ = leftSmoothTripleThird W :=
  pullback.lift_snd _ _ _

/-- Morphisms into the triple product are determined by all three inputs. -/
theorem leftSmoothTriple_hom_ext {X : Scheme.{u}} {f g : X ⟶ leftSmoothTriple W}
    (h₁ : f ≫ leftSmoothTripleFirst W = g ≫ leftSmoothTripleFirst W)
    (h₂ : f ≫ leftSmoothTripleSecond W = g ≫ leftSmoothTripleSecond W)
    (h₃ : f ≫ leftSmoothTripleThird W = g ≫ leftSmoothTripleThird W) : f = g := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [leftSmoothTripleFirst, Category.assoc] using h₁
    · simpa only [leftSmoothTripleSecond, Category.assoc] using h₂
  · exact h₃

/-- The pair consisting of the first sum and the third input. -/
def leftSmoothAddFirstPair : leftSmoothTriple W ⟶ leftSmoothFactorProduct W :=
  pullback.lift (leftSmoothTriplePair W ≫ smoothFactorAddition W)
    (leftSmoothTripleThird W) (by
      rw [Category.assoc, smoothFactorAddition_structure, ← Category.assoc]
      exact leftSmoothTriple_first_third W)

/-- The pair consisting of the first input and the last sum. -/
def leftSmoothAddLastPair : leftSmoothTriple W ⟶ leftSmoothFactorProduct W :=
  pullback.lift (leftSmoothTripleFirst W)
    (leftSmoothTripleLastPair W ≫ leftSmoothFactorAddition W) (by
      rw [Category.assoc, leftSmoothFactorAddition_structure,
        ← Category.assoc (leftSmoothTripleLastPair W), leftSmoothTripleLastPair_fst]
      exact leftSmoothTriple_first_second W)

/-- First coordinate of the left-associated intermediate pair. -/
@[reassoc (attr := simp)] theorem leftSmoothAddFirstPair_fst :
    leftSmoothAddFirstPair W ≫ pullback.fst _ _ =
      leftSmoothTriplePair W ≫ smoothFactorAddition W :=
  pullback.lift_fst _ _ _

/-- Second coordinate of the left-associated intermediate pair. -/
@[reassoc (attr := simp)] theorem leftSmoothAddFirstPair_snd :
    leftSmoothAddFirstPair W ≫ pullback.snd _ _ = leftSmoothTripleThird W :=
  pullback.lift_snd _ _ _

/-- First coordinate of the right-associated intermediate pair. -/
@[reassoc (attr := simp)] theorem leftSmoothAddLastPair_fst :
    leftSmoothAddLastPair W ≫ pullback.fst _ _ = leftSmoothTripleFirst W :=
  pullback.lift_fst _ _ _

/-- Second coordinate of the right-associated intermediate pair. -/
@[reassoc (attr := simp)] theorem leftSmoothAddLastPair_snd :
    leftSmoothAddLastPair W ≫ pullback.snd _ _ =
      leftSmoothTripleLastPair W ≫ leftSmoothFactorAddition W :=
  pullback.lift_snd _ _ _

/-- The constructed left-associated triple sum. -/
def leftSmoothTripleAddLeft : leftSmoothTriple W ⟶ integralCurve W :=
  leftSmoothAddFirstPair W ≫ leftSmoothFactorAddition W

/-- The constructed right-associated triple sum. -/
def leftSmoothTripleAddRight : leftSmoothTriple W ⟶ integralCurve W :=
  leftSmoothAddLastPair W ≫ leftSmoothFactorAddition W

/-- The left-associated triple sum is a morphism over the coefficient spectrum. -/
theorem leftSmoothTripleAddLeft_structure :
    leftSmoothTripleAddLeft W ≫ integralCurveStructure W =
      leftSmoothTripleFirst W ≫ integralSmoothStructure W := by
  rw [leftSmoothTripleAddLeft, Category.assoc, leftSmoothFactorAddition_structure,
    ← Category.assoc, leftSmoothAddFirstPair_fst, Category.assoc,
    smoothFactorAddition_structure, ← Category.assoc]
  rfl

/-- The right-associated triple sum has the same coefficient map. -/
theorem leftSmoothTripleAddRight_structure :
    leftSmoothTripleAddRight W ≫ integralCurveStructure W =
      leftSmoothTripleFirst W ≫ integralSmoothStructure W := by
  rw [leftSmoothTripleAddRight, Category.assoc, leftSmoothFactorAddition_structure,
    ← Category.assoc, leftSmoothAddLastPair_fst]

end FLT.Mazur.WeierstrassIntegralChart

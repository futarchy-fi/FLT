/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothAdditionCommutative

/-!
# Smooth triple products and their two iterated sums

Associativity is an equality on this scheme, rather than on field points.
The universal property gives both intermediate input pairs using the proved
base compatibility of addition. No associativity identity is assumed here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Coefficient map of the actual product. -/
def smoothFactorProductStructure : smoothFactorProduct W ⟶ Spec (.of R) :=
  pullback.fst _ _ ≫ integralSmoothStructure W

/-- The actual fiber product of three copies of the relative smooth curve. -/
abbrev smoothFactorTriple :=
  pullback (smoothFactorProductStructure W) (integralSmoothStructure W)

/-- Projection to the first pair. -/
abbrev smoothFactorTriplePair : smoothFactorTriple W ⟶ smoothFactorProduct W :=
  pullback.fst _ _

/-- First input of the actual triple product. -/
def smoothFactorTripleFirst : smoothFactorTriple W ⟶ (integralSmoothOpen W).toScheme :=
  smoothFactorTriplePair W ≫ pullback.fst _ _

/-- Second input of the actual triple product. -/
def smoothFactorTripleSecond : smoothFactorTriple W ⟶ (integralSmoothOpen W).toScheme :=
  smoothFactorTriplePair W ≫ pullback.snd _ _

/-- Third input of the actual triple product. -/
abbrev smoothFactorTripleThird : smoothFactorTriple W ⟶ (integralSmoothOpen W).toScheme :=
  pullback.snd _ _

/-- The first two inputs have the same coefficient map. -/
theorem smoothFactorTriple_first_second :
    smoothFactorTripleFirst W ≫ integralSmoothStructure W =
      smoothFactorTripleSecond W ≫ integralSmoothStructure W := by
  simp only [smoothFactorTripleFirst, smoothFactorTripleSecond, Category.assoc]
  exact congrArg (fun f => smoothFactorTriplePair W ≫ f) pullback.condition

/-- The first and third inputs have the same coefficient map. -/
theorem smoothFactorTriple_first_third :
    smoothFactorTripleFirst W ≫ integralSmoothStructure W =
      smoothFactorTripleThird W ≫ integralSmoothStructure W := by
  exact (Category.assoc _ _ _).trans pullback.condition

/-- The second and third inputs have the same coefficient map. -/
theorem smoothFactorTriple_second_third :
    smoothFactorTripleSecond W ≫ integralSmoothStructure W =
      smoothFactorTripleThird W ≫ integralSmoothStructure W :=
  (smoothFactorTriple_first_second W).symm.trans (smoothFactorTriple_first_third W)

/-- Projection to the last pair. -/
def smoothFactorTripleLastPair : smoothFactorTriple W ⟶ smoothFactorProduct W :=
  pullback.lift (smoothFactorTripleSecond W) (smoothFactorTripleThird W)
    (smoothFactorTriple_second_third W)

/-- First projection of the last pair. -/
@[reassoc (attr := simp)] theorem smoothFactorTripleLastPair_fst :
    smoothFactorTripleLastPair W ≫ pullback.fst _ _ = smoothFactorTripleSecond W :=
  pullback.lift_fst _ _ _

/-- Second projection of the last pair. -/
@[reassoc (attr := simp)] theorem smoothFactorTripleLastPair_snd :
    smoothFactorTripleLastPair W ≫ pullback.snd _ _ = smoothFactorTripleThird W :=
  pullback.lift_snd _ _ _

/-- Morphisms into the triple product are determined by all three inputs. -/
theorem smoothFactorTriple_hom_ext {X : Scheme.{u}} {f g : X ⟶ smoothFactorTriple W}
    (h₁ : f ≫ smoothFactorTripleFirst W = g ≫ smoothFactorTripleFirst W)
    (h₂ : f ≫ smoothFactorTripleSecond W = g ≫ smoothFactorTripleSecond W)
    (h₃ : f ≫ smoothFactorTripleThird W = g ≫ smoothFactorTripleThird W) : f = g := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [smoothFactorTripleFirst, Category.assoc] using h₁
    · simpa only [smoothFactorTripleSecond, Category.assoc] using h₂
  · exact h₃

/-- The pair consisting of the first sum and the third input. -/
def smoothFactorAddFirstPair : smoothFactorTriple W ⟶ smoothFactorProduct W :=
  pullback.lift (smoothFactorTriplePair W ≫ smoothFactorAddition W)
    (smoothFactorTripleThird W) (by
      rw [Category.assoc, smoothFactorAddition_structure, ← Category.assoc]
      exact smoothFactorTriple_first_third W)

/-- The pair consisting of the first input and the last sum. -/
def smoothFactorAddLastPair : smoothFactorTriple W ⟶ smoothFactorProduct W :=
  pullback.lift (smoothFactorTripleFirst W)
    (smoothFactorTripleLastPair W ≫ smoothFactorAddition W) (by
      rw [Category.assoc, smoothFactorAddition_structure,
        ← Category.assoc (smoothFactorTripleLastPair W), smoothFactorTripleLastPair_fst]
      exact smoothFactorTriple_first_second W)

/-- First coordinate of the left-associated intermediate pair. -/
@[reassoc (attr := simp)] theorem smoothFactorAddFirstPair_fst :
    smoothFactorAddFirstPair W ≫ pullback.fst _ _ =
      smoothFactorTriplePair W ≫ smoothFactorAddition W :=
  pullback.lift_fst _ _ _

/-- Second coordinate of the left-associated intermediate pair. -/
@[reassoc (attr := simp)] theorem smoothFactorAddFirstPair_snd :
    smoothFactorAddFirstPair W ≫ pullback.snd _ _ = smoothFactorTripleThird W :=
  pullback.lift_snd _ _ _

/-- First coordinate of the right-associated intermediate pair. -/
@[reassoc (attr := simp)] theorem smoothFactorAddLastPair_fst :
    smoothFactorAddLastPair W ≫ pullback.fst _ _ = smoothFactorTripleFirst W :=
  pullback.lift_fst _ _ _

/-- Second coordinate of the right-associated intermediate pair. -/
@[reassoc (attr := simp)] theorem smoothFactorAddLastPair_snd :
    smoothFactorAddLastPair W ≫ pullback.snd _ _ =
      smoothFactorTripleLastPair W ≫ smoothFactorAddition W :=
  pullback.lift_snd _ _ _

/-- The constructed left-associated triple sum. -/
def smoothFactorTripleAddLeft : smoothFactorTriple W ⟶ (integralSmoothOpen W).toScheme :=
  smoothFactorAddFirstPair W ≫ smoothFactorAddition W

/-- The constructed right-associated triple sum. -/
def smoothFactorTripleAddRight : smoothFactorTriple W ⟶ (integralSmoothOpen W).toScheme :=
  smoothFactorAddLastPair W ≫ smoothFactorAddition W

/-- The left-associated triple sum is a morphism over the coefficient spectrum. -/
theorem smoothFactorTripleAddLeft_structure :
    smoothFactorTripleAddLeft W ≫ integralSmoothStructure W =
      smoothFactorTripleFirst W ≫ integralSmoothStructure W := by
  rw [smoothFactorTripleAddLeft, Category.assoc, smoothFactorAddition_structure,
    ← Category.assoc, smoothFactorAddFirstPair_fst, Category.assoc,
    smoothFactorAddition_structure, ← Category.assoc]
  rfl

/-- The right-associated triple sum has the same coefficient map. -/
theorem smoothFactorTripleAddRight_structure :
    smoothFactorTripleAddRight W ≫ integralSmoothStructure W =
      smoothFactorTripleFirst W ≫ integralSmoothStructure W := by
  rw [smoothFactorTripleAddRight, Category.assoc, smoothFactorAddition_structure,
    ← Category.assoc, smoothFactorAddLastPair_fst]

end FLT.Mazur.WeierstrassIntegralChart

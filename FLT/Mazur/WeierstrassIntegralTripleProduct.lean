/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAdditionStructure

/-!
# The actual triple product and the two iterated addition maps

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
def integralCurveProductStructure : integralCurveProduct W ⟶ Spec (.of R) :=
  pullback.fst _ _ ≫ integralCurveStructure W

/-- The actual fiber product of three copies of the integral cubic. -/
abbrev integralCurveTriple :=
  pullback (integralCurveProductStructure W) (integralCurveStructure W)

/-- Projection to the first pair. -/
abbrev integralCurveTriplePair : integralCurveTriple W ⟶ integralCurveProduct W :=
  pullback.fst _ _

/-- First input of the actual triple product. -/
def integralCurveTripleFirst : integralCurveTriple W ⟶ integralCurve W :=
  integralCurveTriplePair W ≫ pullback.fst _ _

/-- Second input of the actual triple product. -/
def integralCurveTripleSecond : integralCurveTriple W ⟶ integralCurve W :=
  integralCurveTriplePair W ≫ pullback.snd _ _

/-- Third input of the actual triple product. -/
abbrev integralCurveTripleThird : integralCurveTriple W ⟶ integralCurve W :=
  pullback.snd _ _

/-- The first two inputs have the same coefficient map. -/
theorem integralCurveTriple_first_second :
    integralCurveTripleFirst W ≫ integralCurveStructure W =
      integralCurveTripleSecond W ≫ integralCurveStructure W := by
  simp only [integralCurveTripleFirst, integralCurveTripleSecond, Category.assoc]
  exact congrArg (fun f => integralCurveTriplePair W ≫ f) pullback.condition

/-- The first and third inputs have the same coefficient map. -/
theorem integralCurveTriple_first_third :
    integralCurveTripleFirst W ≫ integralCurveStructure W =
      integralCurveTripleThird W ≫ integralCurveStructure W := by
  exact (Category.assoc _ _ _).trans pullback.condition

/-- The second and third inputs have the same coefficient map. -/
theorem integralCurveTriple_second_third :
    integralCurveTripleSecond W ≫ integralCurveStructure W =
      integralCurveTripleThird W ≫ integralCurveStructure W :=
  (integralCurveTriple_first_second W).symm.trans (integralCurveTriple_first_third W)

/-- Projection to the last pair. -/
def integralCurveTripleLastPair : integralCurveTriple W ⟶ integralCurveProduct W :=
  pullback.lift (integralCurveTripleSecond W) (integralCurveTripleThird W)
    (integralCurveTriple_second_third W)

/-- First projection of the last pair. -/
@[reassoc (attr := simp)] theorem integralCurveTripleLastPair_fst :
    integralCurveTripleLastPair W ≫ pullback.fst _ _ = integralCurveTripleSecond W :=
  pullback.lift_fst _ _ _

/-- Second projection of the last pair. -/
@[reassoc (attr := simp)] theorem integralCurveTripleLastPair_snd :
    integralCurveTripleLastPair W ≫ pullback.snd _ _ = integralCurveTripleThird W :=
  pullback.lift_snd _ _ _

/-- Morphisms into the triple product are determined by all three inputs. -/
theorem integralCurveTriple_hom_ext {X : Scheme.{u}} {f g : X ⟶ integralCurveTriple W}
    (h₁ : f ≫ integralCurveTripleFirst W = g ≫ integralCurveTripleFirst W)
    (h₂ : f ≫ integralCurveTripleSecond W = g ≫ integralCurveTripleSecond W)
    (h₃ : f ≫ integralCurveTripleThird W = g ≫ integralCurveTripleThird W) : f = g := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [integralCurveTripleFirst, Category.assoc] using h₁
    · simpa only [integralCurveTripleSecond, Category.assoc] using h₂
  · exact h₃

variable (hΔ : IsUnit W.Δ)

/-- The pair consisting of the first sum and the third input. -/
def integralCurveAddFirstPair : integralCurveTriple W ⟶ integralCurveProduct W :=
  pullback.lift (integralCurveTriplePair W ≫ integralCurveAddition W hΔ)
    (integralCurveTripleThird W) (by
      rw [Category.assoc, integralCurveAddition_structure, ← Category.assoc]
      exact integralCurveTriple_first_third W)

/-- The pair consisting of the first input and the last sum. -/
def integralCurveAddLastPair : integralCurveTriple W ⟶ integralCurveProduct W :=
  pullback.lift (integralCurveTripleFirst W)
    (integralCurveTripleLastPair W ≫ integralCurveAddition W hΔ) (by
      rw [Category.assoc, integralCurveAddition_structure, ← Category.assoc,
        integralCurveTripleLastPair_fst]
      exact integralCurveTriple_first_second W)

/-- First coordinate of the left-associated intermediate pair. -/
@[reassoc (attr := simp)] theorem integralCurveAddFirstPair_fst :
    integralCurveAddFirstPair W hΔ ≫ pullback.fst _ _ =
      integralCurveTriplePair W ≫ integralCurveAddition W hΔ :=
  pullback.lift_fst _ _ _

/-- Second coordinate of the left-associated intermediate pair. -/
@[reassoc (attr := simp)] theorem integralCurveAddFirstPair_snd :
    integralCurveAddFirstPair W hΔ ≫ pullback.snd _ _ = integralCurveTripleThird W :=
  pullback.lift_snd _ _ _

/-- First coordinate of the right-associated intermediate pair. -/
@[reassoc (attr := simp)] theorem integralCurveAddLastPair_fst :
    integralCurveAddLastPair W hΔ ≫ pullback.fst _ _ = integralCurveTripleFirst W :=
  pullback.lift_fst _ _ _

/-- Second coordinate of the right-associated intermediate pair. -/
@[reassoc (attr := simp)] theorem integralCurveAddLastPair_snd :
    integralCurveAddLastPair W hΔ ≫ pullback.snd _ _ =
      integralCurveTripleLastPair W ≫ integralCurveAddition W hΔ :=
  pullback.lift_snd _ _ _

/-- The constructed left-associated triple sum. -/
def integralCurveTripleAddLeft : integralCurveTriple W ⟶ integralCurve W :=
  integralCurveAddFirstPair W hΔ ≫ integralCurveAddition W hΔ

/-- The constructed right-associated triple sum. -/
def integralCurveTripleAddRight : integralCurveTriple W ⟶ integralCurve W :=
  integralCurveAddLastPair W hΔ ≫ integralCurveAddition W hΔ

/-- The left-associated triple sum is a morphism over the coefficient spectrum. -/
theorem integralCurveTripleAddLeft_structure :
    integralCurveTripleAddLeft W hΔ ≫ integralCurveStructure W =
      integralCurveTripleFirst W ≫ integralCurveStructure W := by
  rw [integralCurveTripleAddLeft, Category.assoc, integralCurveAddition_structure,
    ← Category.assoc, integralCurveAddFirstPair_fst, Category.assoc,
    integralCurveAddition_structure, ← Category.assoc]
  rfl

/-- The right-associated triple sum has the same coefficient map. -/
theorem integralCurveTripleAddRight_structure :
    integralCurveTripleAddRight W hΔ ≫ integralCurveStructure W =
      integralCurveTripleFirst W ≫ integralCurveStructure W := by
  rw [integralCurveTripleAddRight, Category.assoc, integralCurveAddition_structure,
    ← Category.assoc, integralCurveAddLastPair_fst]

end FLT.Mazur.WeierstrassIntegralChart

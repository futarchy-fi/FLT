/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RationalCoefficientSequence
public import FLT.LocalClassFieldTheory.IntegralDegreeTwoComparison
public import FLT.LocalClassFieldTheory.CyclicCarry

/-!
# The cyclic carry is the actual integral connecting class

For the character i ↦ i/n in Q/Z, the categorical continuous boundary is
represented by the positive integer carry. Its sign follows from the differential.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology GaloisRepresentation.Extensions

variable (n : ℕ) [NeZero n]

attribute [local instance] trivialCoefficientAction trivialCoefficientIntComm
  trivialCoefficientContinuous rationalCoefficientTopology rationalCoefficientDiscrete
  rationalCircleCoefficientTopology rationalCircleCoefficientDiscrete

/-- The finite cyclic group has its discrete topology. -/
local instance cyclicCoefficientTopology : TopologicalSpace (Multiplicative (ZMod n)) := ⊥
local instance cyclicCoefficientDiscrete : DiscreteTopology (Multiplicative (ZMod n)) := ⟨rfl⟩

local notation "G" => Multiplicative (ZMod n)

/-- The positive rational-circle character on the finite cyclic group. -/
def cyclicRationalCharacter : ContinuousCocycle G (AddCircle (1 : ℚ)) :=
  ⟨⟨fun g => zmodToRatCircle n g.toAdd, continuous_of_discreteTopology⟩,
    fun g h => by
      change zmodToRatCircle n (g.toAdd + h.toAdd) =
        zmodToRatCircle n h.toAdd + zmodToRatCircle n g.toAdd
      rw [map_add, add_comm]⟩

/-- The rational representative section of the character. -/
def cyclicRationalSection : C(G, ℚ) :=
  ⟨fun g => (g.toAdd.val : ℚ) / n, continuous_of_discreteTopology⟩

/-- The positive integral carry as a jointly continuous cochain. -/
def cyclicIntegralCarry : C(G × G, ℤ) :=
  ⟨fun z => cyclicCarry z.1.toAdd z.2.toAdd, continuous_of_discreteTopology⟩

/-- The carry is an integral cocycle for the trivial action. -/
theorem cyclicIntegralCarry_cocycle : IsCocycle₂ (cyclicIntegralCarry n) := by
  intro g h j
  exact cyclicCarry_cocycle g.toAdd h.toAdd j.toAdd

/-- The rational section lifts the character in the actual continuous complex. -/
theorem cyclicRationalSection_lifts :
    ((continuousCoefficientMap (rationalCircleProjection G)).f 1).hom
        (continuousOneCochain (k := ℤ) (cyclicRationalSection n)) =
      continuousOneCochain (k := ℤ) (cyclicRationalCharacter n).val := by
  apply Subtype.ext
  funext x
  exact cyclicCarry_section (x 0).toAdd

/-- The lifted differential is exactly the included positive carry. -/
theorem cyclicRationalSection_d :
    ((continuousCoefficientMap (integralRationalInclusion G)).f 2).hom
        (continuousTwoCochain (k := ℤ) (cyclicIntegralCarry n)) =
      ((continuousCochains ℤ G ℚ).d 1 2).hom
        (continuousOneCochain (k := ℤ) (cyclicRationalSection n)) := by
  apply Subtype.ext
  funext x
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  rw [hx, continuous_d_one]
  exact cyclicCarry_rat (x 0).toAdd (x 1).toAdd

/-- The actual Q/Z-to-Z boundary sends i/n to the positive carry class. -/
theorem rationalIntegralConnectingMap_cyclicCarry :
    (rationalIntegralConnectingMap G 1).hom
        (integralH1Class (k := ℤ) (cyclicRationalCharacter n)) =
      integralH2Class (k := ℤ) (cyclicIntegralCarry n) (cyclicIntegralCarry_cocycle n) := by
  exact continuousConnectingMap_apply _ _ _ _ _ _ 1
    (continuousOneCochain (cyclicRationalCharacter n).val)
    ((continuousOneCochain_cycle_iff (k := ℤ) _).mpr (cyclicRationalCharacter n).property)
    (continuousOneCochain (cyclicRationalSection n)) (cyclicRationalSection_lifts n)
    (continuousTwoCochain (cyclicIntegralCarry n)) (cyclicRationalSection_d n)

end LocalClassFieldTheory

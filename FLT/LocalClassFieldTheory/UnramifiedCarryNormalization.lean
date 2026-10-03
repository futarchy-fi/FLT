/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedIntegralH2Additive
public import FLT.LocalClassFieldTheory.TrivialRestrictionNaturality
public import FLT.LocalClassFieldTheory.CyclicCarryConnecting

/-!
# Positive carry normalization in the unramified quotient

Inflating the actual cyclic carry class from degree n has Frobenius coordinate
1/n. This follows from the proved connecting-map square, including its sign.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory HomologicalComplex

attribute [local instance] trivialCoefficientAction trivialCoefficientIntComm
  trivialCoefficientContinuous rationalCircleCoefficientTopology rationalCircleCoefficientDiscrete

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]


local notation "U" => maximalUnramified R K C
local notation "Frob" => unramifiedFrobenius R K C

attribute [local instance] unramifiedH2Galois

/-- Inflate the positive finite cyclic carry to the constructed unramified quotient. -/
def unramifiedCarryClass (n : UnramifiedIndex) : continuousCohomology ℤ Gal(U/K) ℤ 2 :=
  (homologyMap (trivialRestriction (unramifiedDegreeCharacter R K C n) ℤ) 2).hom
    (integralH2Class (k := ℤ) (cyclicIntegralCarry n.degree) (cyclicIntegralCarry_cocycle n.degree))

/-- The inflated carry is the actual connecting class of the normalized degree character. -/
theorem unramifiedCarryClass_character (n : UnramifiedIndex) :
    unramifiedCarryClass R K C n =
      integralH2CharacterEquiv Gal(U/K) (unramifiedRationalCircleCharacter R K C n) := by
  let χ := cocycleCharacter (cyclicRationalCharacter n.degree)
  have hc : integralH2CharacterEquiv (Multiplicative (ZMod n.degree)) χ =
      integralH2Class (k := ℤ) (cyclicIntegralCarry n.degree)
        (cyclicIntegralCarry_cocycle n.degree) := by
    rw [integralH2CharacterEquiv_apply]
    exact rationalIntegralConnectingMap_cyclicCarry n.degree
  unfold unramifiedCarryClass
  rw [← hc, integralH2CharacterEquiv_restriction]
  apply congrArg (integralH2CharacterEquiv Gal(U/K))
  ext σ
  rfl

/-- The actual inflated carry has positive Frobenius coordinate 1/n. -/
theorem unramifiedCarryClass_coordinate (n : UnramifiedIndex) :
    unramifiedIntegralH2AddEquiv R K C (unramifiedCarryClass R K C n) =
      (↑((1 : ℚ) / n.degree) : AddCircle (1 : ℚ)) := by
  change unramifiedIntegralH2Equiv R K C (unramifiedCarryClass R K C n) = _
  rw [unramifiedCarryClass_character, unramifiedIntegralH2Equiv_degree]

/-- Integer multiples of the inflated carry have the expected rational-circle coordinates. -/
theorem unramifiedCarryClass_zsmul_coordinate (n : UnramifiedIndex) (j : ℤ) :
    unramifiedIntegralH2AddEquiv R K C (j • unramifiedCarryClass R K C n) =
      (↑((j : ℚ) / n.degree) : AddCircle (1 : ℚ)) := by
  rw [map_zsmul, unramifiedCarryClass_coordinate, ← AddCircle.coe_zsmul]
  congr 1
  simp [zsmul_eq_mul, div_eq_mul_inv]

end LocalClassFieldTheory

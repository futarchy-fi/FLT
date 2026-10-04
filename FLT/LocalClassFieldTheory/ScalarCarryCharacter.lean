/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CharacterFieldCarry
public import FLT.LocalClassFieldTheory.CyclicCarryConnecting
public import FLT.LocalClassFieldTheory.TrivialRestrictionNaturality

/-!
# The integral carry for an arbitrary continuous finite character

The actual positive connecting map identifies the integral carry with the
rational-circle character, by restriction of the cyclic calculation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory HomologicalComplex

attribute [local instance] trivialCoefficientAction trivialCoefficientIntComm
  trivialCoefficientContinuous rationalCircleCoefficientTopology rationalCircleCoefficientDiscrete

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] {n : ℕ} [NeZero n]

/-- The rational-circle character associated to a finite scalar character. -/
def scalarRationalCharacter (χ : ContinuousScalarCharacter G (ZMod n)) :
    G →ₜ* Multiplicative (AddCircle (1 : ℚ)) :=
  (cocycleCharacter (cyclicRationalCharacter n)).comp (scalarCharacterHom χ)

/-- The actual continuous integral class of the positive scalar carry. -/
def scalarCarryClass (χ : ContinuousScalarCharacter G (ZMod n)) :
    continuousCohomology ℤ G ℤ 2 :=
  integralH2Class (k := ℤ) (cyclicParameterCarry χ (1 : ℤ))
    (cyclicParameterCarry_isCocycle χ 1 (fun _ => rfl))

/-- The positive connecting character is represented by the positive integral carry. -/
theorem scalarCarryClass_character (χ : ContinuousScalarCharacter G (ZMod n)) :
    scalarCarryClass χ = integralH2CharacterEquiv G (scalarRationalCharacter χ) := by
  let ψ := cocycleCharacter (cyclicRationalCharacter n)
  have hc : integralH2CharacterEquiv (Multiplicative (ZMod n)) ψ =
      integralH2Class (k := ℤ) (cyclicIntegralCarry n) (cyclicIntegralCarry_cocycle n) := by
    rw [integralH2CharacterEquiv_apply]
    exact rationalIntegralConnectingMap_cyclicCarry n
  rw [scalarRationalCharacter, ← integralH2CharacterEquiv_restriction, hc]
  have he := continuousInflationH2_class (scalarCharacterHom χ).toMonoidHom
    (scalarCharacterHom χ).continuous
    (trivialRestrictionCoefficient (scalarCharacterHom χ).toMonoidHom ℤ)
    (cyclicIntegralCarry n) (cyclicIntegralCarry_cocycle n)
  refine Eq.trans ?_ he.symm
  unfold scalarCarryClass
  congr 1
  apply ContinuousMap.ext
  intro z
  change cyclicCarry (χ.val z.1) (χ.val z.2) • (1 : ℤ) =
    cyclicCarry (χ.val z.1) (χ.val z.2)
  simp

end LocalClassFieldTheory

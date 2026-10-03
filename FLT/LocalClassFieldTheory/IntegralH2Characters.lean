/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TrivialH1Characters
public import FLT.LocalClassFieldTheory.RationalIntegralConnectingIso

/-!
# Integral H2 and rational-circle characters

The character description of H1 followed by the positive connecting
isomorphism gives the character description of integral H2.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

attribute [local instance] trivialCoefficientAction trivialCoefficientIntComm
  trivialCoefficientContinuous rationalCoefficientTopology rationalCoefficientDiscrete
  rationalCircleCoefficientTopology rationalCircleCoefficientDiscrete

/-- Every continuous rational-circle character determines exactly one integral H2 class. -/
def integralH2CharacterEquiv :
    (G →ₜ* Multiplicative (AddCircle (1 : ℚ))) ≃ continuousCohomology ℤ G ℤ 2 :=
  trivialH1CharacterEquiv.symm.trans
    ((rationalIntegralConnectingIso G 0).toLinearEquiv.toEquiv)

/-- The character-to-H2 equivalence is the actual positive connecting map. -/
theorem integralH2CharacterEquiv_apply (χ : G →ₜ* Multiplicative (AddCircle (1 : ℚ))) :
    integralH2CharacterEquiv G χ = (rationalIntegralConnectingMap G 1).hom
      (integralH1Class (k := ℤ) (characterCocycle χ)) := by
  apply congrArg (rationalIntegralConnectingMap G 1).hom
  exact trivialH1CharacterEquiv.symm_apply_eq.mpr (trivialH1CharacterEquiv_class χ).symm

/-- Equality of integral H2 classes is equality of their continuous characters. -/
theorem integralH2CharacterEquiv_injective : Function.Injective (integralH2CharacterEquiv G) :=
  (integralH2CharacterEquiv G).injective

/-- Every integral H2 class is the boundary of a continuous rational-circle character. -/
theorem integralH2CharacterEquiv_surjective : Function.Surjective (integralH2CharacterEquiv G) :=
  (integralH2CharacterEquiv G).surjective

end LocalClassFieldTheory

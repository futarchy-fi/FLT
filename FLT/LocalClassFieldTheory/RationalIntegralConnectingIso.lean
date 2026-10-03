/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RationalCoefficientSequence
public import FLT.LocalClassFieldTheory.IntegralRationalVanishing

/-!
# Positive rational-integral connecting isomorphisms

The connecting map for Z to Q to Q/Z is an isomorphism in positive degrees.
Both adjacent rational cohomology groups vanish in the integral complex.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

attribute [local instance] trivialCoefficientAction trivialCoefficientIntComm
  trivialCoefficientContinuous rationalCoefficientTopology rationalCoefficientDiscrete
  rationalCircleCoefficientTopology rationalCircleCoefficientDiscrete

local instance trivialRationalCoefficientComm : SMulCommClass G ℚ ℚ := ⟨fun _ _ _ => rfl⟩

/-- Both adjacent rational terms vanish, so the positive boundary is invertible. -/
theorem rationalIntegralConnectingMap_isIso (n : ℕ) :
    IsIso (rationalIntegralConnectingMap G (n + 1)) :=
  (rationalCoefficientSequence_shortExact G).isIso_δ (n + 1) (n + 2) rfl
    (integralRational_cohomology_isZero (G := G) (M := ℚ) n)
    (integralRational_cohomology_isZero (G := G) (M := ℚ) (n + 1))

/-- Positive-degree Q/Z cohomology is the next integral cohomology group. -/
def rationalIntegralConnectingIso (n : ℕ) :
    (continuousCochains ℤ G (AddCircle (1 : ℚ))).homology (n + 1) ≅
      (continuousCochains ℤ G ℤ).homology (n + 2) :=
  @asIso _ _ _ _ (rationalIntegralConnectingMap G (n + 1))
    (rationalIntegralConnectingMap_isIso G n)

/-- The degree-one/two identification uses the constructed boundary, with its proved sign. -/
theorem rationalIntegralConnectingIso_hom (n : ℕ) :
    (rationalIntegralConnectingIso G n).hom = rationalIntegralConnectingMap G (n + 1) := rfl

end LocalClassFieldTheory

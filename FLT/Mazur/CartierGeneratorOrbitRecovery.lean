/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupOrbitMarking

/-!
# Orbit reconstruction recovers the specified Cartier generator

When the prescribed curve marking comes from an existing generator, lifting
its label one to the actual subgroup recovers that generator itself.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ} [NeZero n]
  (H : E.FiniteSubgroup n) {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  (hI : H.ideal = E.cyclicMarkingIdeal φ) (hφ : H.generatorCurveMarking hP = φ)

include hφ

/-- Lifting each specified generator label recovers its original subgroup section. -/
theorem orbitMarking_eq_generatorPowers (i : Multiplicative (ZMod n)) :
    H.orbitMarking φ hI i = H.generatorPowers P hP.1 i := by
  let _ : Mono H.inclusion := Over.mono_of_mono_left H.inclusion
  apply (cancel_mono H.inclusion).mp
  rw [orbitMarking_inclusion, ← hφ]
  rfl

/-- The orbit construction recovers the specified generator, including for order one. -/
theorem orbitGenerator_eq_of_generatorMarking : H.orbitGenerator φ hI = P := by
  dsimp only [orbitGenerator]
  rw [H.orbitMarking_eq_generatorPowers hP φ hI hφ]
  simpa only [Nat.cast_one, pow_one] using H.generatorPowers_natCast P hP.1 1

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

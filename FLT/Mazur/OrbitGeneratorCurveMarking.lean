/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierGeneratorOrbitRecovery

/-!
# Recover the curve marking from the constructed orbit generator

The Cartier generator obtained from label one recovers every input label,
including when different labels coincide on the base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ} [NeZero n]
  (H : E.FiniteSubgroup n)
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  (hI : H.ideal = E.cyclicMarkingIdeal φ)
  [SmoothOfRelativeDimension 1 E.curve.hom]

/-- The reconstructed generator induces precisely the given full cyclic marking. -/
theorem orbitGenerator_curveMarking :
    H.generatorCurveMarking (H.orbitGenerator_cartier φ hI) = φ := by
  apply MonoidHom.ext
  intro i
  change (H.orbitGenerator φ hI ^ i.toAdd.val) ≫ H.inclusion = φ i
  rw [orbitGenerator_pow, orbitMarking_inclusion]
  rw [ZMod.natCast_zmod_val]
  rfl

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

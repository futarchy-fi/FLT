/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicOrbitSubgroupMarking
public import FLT.Mazur.GeneralizedCurveCyclicSubgroup

/-!
# The orbit ideal supplies an actual Cartier generator

The lifted label one generates the full orbit divisor scheme-theoretically.
Coincident sections retain their multiplicities, so the result does not
require an etale subgroup or a reduced base.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ} [NeZero n]
  (H : E.FiniteSubgroup n)
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  (hI : H.ideal = E.cyclicMarkingIdeal φ)

/-- The actual subgroup section lying over the cyclic label one. -/
def orbitGenerator : 𝟙_ (Over S) ⟶ H.carrier := H.orbitMarking φ hI (.ofAdd 1)

/-- The powers of label one recover all original cyclic labels on the subgroup. -/
theorem orbitGenerator_pow (m : ℕ) :
    H.orbitGenerator φ hI ^ m = H.orbitMarking φ hI (.ofAdd (m : ZMod n)) := by
  simp only [orbitGenerator, ← map_pow, ← ofAdd_nsmul,
    nsmul_eq_mul, _root_.mul_one]

/-- The lifted generator is killed by the original cyclic order. -/
theorem orbitGenerator_torsion : H.orbitGenerator φ hI ^ n = 1 := by
  rw [orbitGenerator_pow, ZMod.natCast_self]
  exact map_one _

/-- Each power recovers its original full-curve section, with no distinctness assumption. -/
theorem orbitGenerator_pow_curveMap (m : ℕ) :
    (H.orbitGenerator φ hI ^ m) ≫ H.curveMap = φ (.ofAdd (m : ZMod n)) ≫ E.inclusion := by
  rw [orbitGenerator_pow]
  exact H.orbitSection_curveMap φ hI _

variable [SmoothOfRelativeDimension 1 E.curve.hom]

/-- The lifted section is an actual Cartier generator of the full orbit subgroup. -/
theorem orbitGenerator_cartier : H.IsCartierGenerator (H.orbitGenerator φ hI) := by
  refine ⟨H.orbitGenerator_torsion φ hI, ?_, ?_⟩
  · rw [hI]
    exact E.cyclicMarkingIdeal_cartier φ
  · rw [hI, cyclicMarkingIdeal]
    apply Finset.prod_congr rfl
    intro i _
    rw [orbitGenerator_pow_curveMap]

include hI in
/-- An orbit subgroup is cyclic in the fppf Cartier-generator sense. -/
theorem isCyclic_of_orbitIdeal : H.IsCyclic := (H.orbitGenerator_cartier φ hI).isCyclic H

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

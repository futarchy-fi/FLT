/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierFppfDescent
public import FLT.Mazur.GeneralizedCurveCartierStalks

/-!
# Global Cartier divisors of cyclic finite subgroups

The Cartier equations of an fppf-local generator descend to actual affine
Cartier neighborhoods. Combined with the unconditional flatness of the finite
subgroup divisor, this proves the global relative Cartier condition.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ} (H : E.FiniteSubgroup n)

/-- An fppf-cyclic subgroup defines an effective Cartier divisor globally. -/
theorem IsCyclic.effectiveCartier (hH : H.IsCyclic) : FCurve.EffectiveCartier H.ideal := by
  obtain ⟨U, g, hg, hs, hl, P, hP⟩ := hH
  let := hg
  let := hs
  let := hl
  apply FCurve.effectiveCartier_of_fppf_comap H.ideal (pullback.fst E.curve.hom g)
  simpa only [baseChange_ideal] using hP.2.1.1

/-- The actual divisor of a cyclic finite subgroup is relative effective Cartier. -/
theorem IsCyclic.relativeEffectiveCartier (hH : H.IsCyclic) :
    FCurve.RelativeEffectiveCartier E.curve.hom H.ideal :=
  (H.relativeCartier_iff_effectiveCartier).mpr (hH.effectiveCartier H)

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

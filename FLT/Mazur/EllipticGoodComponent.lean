/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticComponentQuotient
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# The good-reduction component quotient

If the special cubic is elliptic, every primitive reduction is nonsingular.
Consequently E₀ is the entire generic point group and E/E₀ is trivial.
The final theorem applies Mathlib's good-reduction predicate to its chosen
integral model. Neither completeness nor a Néron model is needed for this case.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve WeierstrassCurve.Projective

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- A smooth special cubic makes every generic point belong to E₀. -/
theorem smoothReduction_of_isElliptic [(W.map (residue A)).IsElliptic]
    (P : (W.map (algebraMap A K)).toProjective.Point) : SmoothReduction A W P := by
  let v := primitiveLift A W P
  by_cases hz : residue A (v.coords 2) = 0
  · exact ((infinityReduction_iff_residue_z A W v).mpr hz).smooth A W
  · change (W.map (residue A)).toProjective.NonsingularLift _
    rw [projectiveReduction_eq A W P v]
    apply (nonsingular_of_Z_ne_zero hz).mpr
    exact Affine.equation_iff_nonsingular.mp
      ((equation_of_Z_ne_zero hz).mp (v.residue_equation A W))

/-- In good reduction the nonsingular-reduction subgroup is the entire group. -/
theorem ellipticE0_eq_top_of_isElliptic [(W.map (residue A)).IsElliptic] :
    ellipticE0 A W = ⊤ := by
  apply top_unique
  intro P _
  exact smoothReduction_of_isElliptic A W P

/-- Every component class vanishes in good reduction. -/
theorem ellipticComponent_eq_zero_of_isElliptic [(W.map (residue A)).IsElliptic]
    (c : EllipticComponentQuotient A W) : c = 0 := by
  obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A W c
  exact (ellipticComponentHom_eq_zero A W P).mpr (smoothReduction_of_isElliptic A W P)

/-- The actual rational component quotient in good reduction is trivial. -/
theorem ellipticComponent_subsingleton_of_isElliptic [(W.map (residue A)).IsElliptic] :
    Subsingleton (EllipticComponentQuotient A W) :=
  ⟨fun c d => (ellipticComponent_eq_zero_of_isElliptic A W c).trans
    (ellipticComponent_eq_zero_of_isElliptic A W d).symm⟩

/-- Mathlib's good minimal model has trivial rational component quotient. -/
theorem ellipticComponent_subsingleton_of_goodReduction [IsDiscreteValuationRing A]
    (E : WeierstrassCurve K) [E.HasGoodReduction A] :
    Subsingleton (EllipticComponentQuotient A (E.integralModel A)) := by
  have : ((E.integralModel A).map (residue A)).IsElliptic :=
    (hasGoodReduction_iff_isElliptic_reduction A).mp inferInstance
  exact ellipticComponent_subsingleton_of_isElliptic A _

end FLT.Mazur

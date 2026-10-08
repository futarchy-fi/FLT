/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PowerCohomologyShift
public import FLT.Mazur.ReesAlgebraDirectSum

/-!
# The genuine Rees action on all power cohomology

Homogeneous multiplication on the original sheaves assembles to a ring
representation on the direct sum of their cohomology. Restrict this
representation along the actual polynomial Rees coordinate equivalence.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.GlobalIdealPower
open scoped DirectSum

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]
  (J : Ideal R)
  (hJ : ∀ r : R, r ∈ J → ∀ U : X.affineOpens,
    X.presheaf.map U.1.leTop.op (ρ r) ∈ I.ideal U)
  (q : ℕ)

/-- Additive homogeneous coefficients act on the original cohomology sum. -/
def powerShiftAdd (a : ℕ) : ↥(J ^ a) →+ Module.End R (PowerCohomologySum ρ I M q) :=
  AddMonoidHom.mk' (powerShift ρ I M J hJ q a) (powerShift_add ρ I M J hJ q a)

/-- Homogeneous scalars assemble to a ring representation. -/
def powerGradedRepresentation :
    (⨁ a : ℕ, ↥(J ^ a)) →+* Module.End R (PowerCohomologySum ρ I M q) :=
  DirectSum.toSemiring (powerShiftAdd ρ I M J hJ q)
    (powerShift_one ρ I M J hJ q) (fun {a b} r s ↦ powerShift_mul ρ I M J hJ q a b r s)

/-- The polynomial Rees algebra acts through its actual homogeneous coefficients. -/
def powerReesRepresentation :
    reesAlgebra J →+* Module.End R (PowerCohomologySum ρ I M q) :=
  (powerGradedRepresentation ρ I M J hJ q).comp (Rees.sumRingEquiv J).symm.toRingHom

/-- The full power cohomology sum carries its original Rees action. -/
@[instance_reducible]
def powerReesModule : Module (reesAlgebra J) (PowerCohomologySum ρ I M q) :=
  Module.compHom _ (powerReesRepresentation ρ I M J hJ q)

/-- Every Rees monomial acts by cohomology of its original scalar lift. -/
lemma powerReesRepresentation_monomial (a : ℕ) (r : ↥(J ^ a)) :
    powerReesRepresentation ρ I M J hJ q (Rees.monomial J a r) =
      powerShift ρ I M J hJ q a r := by
  have h : (Rees.sumRingEquiv J).symm (Rees.monomial J a r) =
      DirectSum.of (fun n ↦ ↥(J ^ n)) a r := by
    apply (Rees.sumRingEquiv J).injective
    exact (Rees.sumRingEquiv J).apply_symm_apply _ |>.trans (Rees.sumRingHom_of J a r).symm
  change powerGradedRepresentation ρ I M J hJ q
    ((Rees.sumRingEquiv J).symm (Rees.monomial J a r)) = _
  rw [h]
  exact DirectSum.toSemiring_of _ _ _ _ _

/-- The constructed action retains the degree and map of each original power class. -/
lemma powerReesModule_monomial_of (a n : ℕ) (r : ↥(J ^ a))
    (x : ModuleRingH ρ (power I n M) q) :
    let _ := powerReesModule ρ I M J hJ q
    Rees.monomial J a r • (DirectSum.lof R ℕ _ n x : PowerCohomologySum ρ I M q) =
      DirectSum.lof R ℕ _ (a + n)
        (((moduleRingHFunctor ρ q).map (powerScalarMap ρ I M J hJ a n r)).hom x) := by
  change powerReesRepresentation ρ I M J hJ q (Rees.monomial J a r)
    (DirectSum.lof R ℕ _ n x) = _
  rw [powerReesRepresentation_monomial, powerShift_of]

end FLT.Mazur.IdealAdicQuotient

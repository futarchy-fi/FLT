/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PowerCohomologyReesAction

/-!
# Rees linearity of the original power cohomology comparison

The comparison respects homogeneous multiplication because the original
scalar lifts factor scalar multiplication through the original inclusions.
Assembly gives a Rees-linear surjection onto the actual image Rees module.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.GlobalIdealPower FLT.Mazur.IdealPowerScalarLift
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

/-- The original comparison intertwines each homogeneous shift with polynomial multiplication. -/
lemma powerCohomologyComparison_shift (a : ℕ) (r : ↥(J ^ a))
    (x : PowerCohomologySum ρ I M q) :
    powerCohomologyComparison ρ I M q (powerShift ρ I M J hJ q a r x) =
      Rees.monomial J a r • powerCohomologyComparison ρ I M q x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | of n x =>
    change powerCohomologyComparison ρ I M q
      (powerShift ρ I M J hJ q a r (DirectSum.lof R ℕ _ n x)) =
      Rees.monomial J a r • powerCohomologyComparison ρ I M q (DirectSum.lof R ℕ _ n x)
    rw [powerShift_of, powerCohomologyComparison_of, powerCohomologyComparison_of]
    change PolynomialModule.single (M := ModuleRingH ρ M q) R (a + n)
        (moduleHMap (inclusion (I ^ (a + n)) M) q
          (moduleHMap (powerScalarMap ρ I M J hJ a n r) q x)) =
      Polynomial.monomial a r.val • PolynomialModule.single (M := ModuleRingH ρ M q) R n
        (moduleHMap (inclusion (I ^ n) M) q x)
    rw [PolynomialModule.monomial_smul_single, ← LinearMap.comp_apply,
      ← moduleHMap_comp, powerScalarMap_inclusion, moduleHMap_comp, LinearMap.comp_apply,
      scalarEnd_cohomology, _root_.map_smul]
    rfl

/-- Every Rees coefficient respects the original comparison on all cohomology classes. -/
lemma powerCohomologyComparison_rees_smul (p : reesAlgebra J)
    (x : PowerCohomologySum ρ I M q) :
    let _ := powerReesModule ρ I M J hJ q
    powerCohomologyComparison ρ I M q (p • x) =
      p • powerCohomologyComparison ρ I M q x := by
  let _ := powerReesModule ρ I M J hJ q
  obtain ⟨p, rfl⟩ := (Rees.sumRingEquiv J).surjective p
  induction p using DirectSum.induction_on with
  | zero => simp only [map_zero, zero_smul]
  | add p t hp ht => simp only [map_add, add_smul, hp, ht]
  | of a r =>
    change powerCohomologyComparison ρ I M q
      (powerReesRepresentation ρ I M J hJ q (Rees.sumRingHom J
        (DirectSum.of (fun n ↦ ↥(J ^ n)) a r)) x) =
      Rees.sumRingHom J (DirectSum.of (fun n ↦ ↥(J ^ n)) a r) •
        powerCohomologyComparison ρ I M q x
    rw [Rees.sumRingHom_of, powerReesRepresentation_monomial]
    exact powerCohomologyComparison_shift ρ I M J hJ q a r x

/-- The original direct-sum comparison is linear over the genuine Rees algebra. -/
def powerReesComparison :
    let _ := powerReesModule ρ I M J hJ q
    PowerCohomologySum ρ I M q →ₗ[reesAlgebra J]
      PolynomialModule R (ModuleRingH ρ M q) :=
  let _ := powerReesModule ρ I M J hJ q
  { (powerCohomologyComparison ρ I M q).toAddMonoidHom with
    map_smul' := powerCohomologyComparison_rees_smul ρ I M J hJ q }

/-- Its Rees-linear range is precisely the actual cohomology image module. -/
lemma powerReesComparison_range :
    let _ := powerReesModule ρ I M J hJ q
    LinearMap.range (powerReesComparison ρ I M J hJ q) = cohomologyRees ρ I M J hJ q := by
  let _ := powerReesModule ρ I M J hJ q
  ext p
  exact SetLike.ext_iff.mp (powerCohomologyComparison_range ρ I M J hJ q) p

end FLT.Mazur.IdealAdicQuotient

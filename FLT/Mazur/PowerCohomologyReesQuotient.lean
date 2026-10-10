/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PowerCohomologyReesComparison

/-!
# The actual image Rees module as a quotient of power cohomology

The full power-cohomology comparison surjects onto the actual image module.
Its kernel consists exactly of classes killed degreewise by the original
power inclusions. The quotient identification is linear over the Rees ring.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

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

omit [IsLocallyNoetherian X] [M.IsFinitePresentation] in
/-- Each coefficient is the image of the original class in that degree. -/
lemma powerCohomologyComparison_coeff (x : PowerCohomologySum ρ I M q) (n : ℕ) :
    (powerCohomologyComparison ρ I M q x).coeff n =
      ((moduleRingHFunctor ρ q).map (inclusion (I ^ n) M)).hom (x n) := by
  classical
  induction x using DirectSum.induction_on with
  | zero =>
    change (powerCohomologyComparison ρ I M q 0).coeff n =
      ((moduleRingHFunctor ρ q).map (inclusion (I ^ n) M)).hom 0
    simp only [map_zero, PolynomialModule.coeff_zero, Finsupp.zero_apply]
  | add x y hx hy =>
    rw [map_add, PolynomialModule.coeff_add, Finsupp.add_apply, hx, hy]
    exact (map_add _ _ _).symm
  | of k x =>
    change (powerCohomologyComparison ρ I M q (DirectSum.lof R ℕ _ k x)).coeff n = _
    rw [powerCohomologyComparison_of]
    by_cases h : k = n
    · subst n
      simp only [PolynomialModule.coeff_single, Finsupp.single_eq_same, DirectSum.of_eq_same]
    · simp only [PolynomialModule.coeff_single, Finsupp.single_apply, ite_eq_right h,
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), map_zero]

/-- The original comparison, with codomain its actual image Rees module. -/
def powerReesOnto :
    let _ := powerReesModule ρ I M J hJ q
    PowerCohomologySum ρ I M q →ₗ[reesAlgebra J] cohomologyRees ρ I M J hJ q := by
  let _ := powerReesModule ρ I M J hJ q
  exact (powerReesComparison ρ I M J hJ q).codRestrict _ (fun x ↦ by
    rw [← powerReesComparison_range]
    exact ⟨x, rfl⟩)

/-- Every actual image class lifts through the original full power-cohomology comparison. -/
lemma powerReesOnto_surjective :
    let _ := powerReesModule ρ I M J hJ q
    Function.Surjective (powerReesOnto ρ I M J hJ q) := by
  let _ := powerReesModule ρ I M J hJ q
  dsimp only
  intro y
  have hy : y.val ∈ LinearMap.range (powerReesComparison ρ I M J hJ q) :=
    (powerReesComparison_range ρ I M J hJ q).ge y.property
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

/-- The kernel retains exactly the degreewise kernels of the original inclusions. -/
lemma mem_powerReesComparison_ker (x : PowerCohomologySum ρ I M q) :
    let _ := powerReesModule ρ I M J hJ q
    x ∈ LinearMap.ker (powerReesComparison ρ I M J hJ q) ↔
      ∀ n, moduleHMap (inclusion (I ^ n) M) q (x n) = 0 := by
  let _ := powerReesModule ρ I M J hJ q
  change powerCohomologyComparison ρ I M q x = 0 ↔ _
  constructor
  · intro h n
    change ((moduleRingHFunctor ρ q).map (inclusion (I ^ n) M)).hom (x n) = 0
    have hc := congrArg (fun p : PolynomialModule R (ModuleRingH ρ M q) ↦ p.coeff n) h
    simpa only [powerCohomologyComparison_coeff, PolynomialModule.coeff_zero,
      Finsupp.zero_apply] using hc
  · intro h
    apply PolynomialModule.ext
    ext n
    exact (powerCohomologyComparison_coeff ρ I M q x n).trans (h n)

/-- The actual cohomology image Rees module is the quotient by this genuine kernel. -/
def powerReesQuotientEquiv :
    let _ := powerReesModule ρ I M J hJ q
    (PowerCohomologySum ρ I M q ⧸ LinearMap.ker (powerReesComparison ρ I M J hJ q))
      ≃ₗ[reesAlgebra J] cohomologyRees ρ I M J hJ q :=
  let _ := powerReesModule ρ I M J hJ q
  (powerReesComparison ρ I M J hJ q).quotKerEquivRange |>.trans
    (LinearEquiv.ofEq _ _ (powerReesComparison_range ρ I M J hJ q))

end FLT.Mazur.IdealAdicQuotient

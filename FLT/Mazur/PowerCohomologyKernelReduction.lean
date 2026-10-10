/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PowerCohomologyKernelScalar
public import FLT.Mazur.PowerCohomologyKernelGenerators

/-!
# Reduction of high-degree kernel generators

At a fixed target power, every sufficiently high coordinate of every Rees
multiple of a bounded-degree inclusion-kernel generator reduces to zero.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.GlobalIdealPower
open FLT.Mazur.GlobalIdealPowerCompatibility
open scoped DirectSum

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]
  (J : Ideal R)
  (hJ : ∀ r : R, r ∈ J → ∀ U : X.affineOpens,
    X.presheaf.map U.1.leTop.op (ρ r) ∈ I.ideal U) (q : ℕ)

/-- Take one original power-cohomology coordinate and reduce it to a lower power. -/
def powerTransitionComponent {b d : ℕ} (hbd : b ≤ d) :
    PowerCohomologySum ρ I M q →ₗ[R] ModuleRingH ρ (power I b M) q :=
  ((moduleRingHFunctor ρ q).map (transition I M hbd)).hom.comp
    (DirectSum.component R ℕ _ d)

/-- Component reduction uses the original transition on the chosen coefficient. -/
lemma powerTransitionComponent_apply {b d : ℕ} (hbd : b ≤ d)
    (x : PowerCohomologySum ρ I M q) :
    powerTransitionComponent ρ I M q hbd x = moduleHMap (transition I M hbd) q (x d) := rfl

/-- High coordinates of a monomial multiple of an inclusion-kernel generator reduce to zero. -/
lemma powerTransitionComponent_monomial_kernel (b d n : ℕ) (hbd : b ≤ d)
    (hd : b + n ≤ d) (a : ℕ) (r : ↥(J ^ a))
    (x : ModuleRingH ρ (power I n M) q)
    (hx : moduleHMap (inclusion (I ^ n) M) q x = 0) :
    let _ := powerReesModule ρ I M J hJ q
    powerTransitionComponent ρ I M q hbd
      (Rees.monomial J a r • (DirectSum.lof R ℕ _ n x)) = 0 := by
  let _ := powerReesModule ρ I M J hJ q
  dsimp only
  rw [powerReesModule_monomial_of]
  rw [powerTransitionComponent_apply]
  by_cases he : a + n = d
  · subst d
    have hba : b ≤ a := Nat.le_of_add_le_add_right hd
    change moduleHMap (transition I M hbd) q
      ((DirectSum.of (fun k ↦ ModuleRingH ρ (power I k M) q) (a + n) _) (a + n)) = 0
    rw [DirectSum.of_eq_same]
    exact powerScalarMap_kernel_transition_zero ρ I M J hJ q a b n hba r x hx
  · change moduleHMap (transition I M hbd) q
      ((DirectSum.of (fun k ↦ ModuleRingH ρ (power I k M) q) (a + n) _) d) = 0
    rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm he), map_zero]

/-- Every Rees coefficient has the same vanishing bound on an original homogeneous kernel. -/
lemma powerTransitionComponent_rees_kernel (b d n : ℕ) (hbd : b ≤ d)
    (hd : b + n ≤ d) (p : reesAlgebra J)
    (x : ModuleRingH ρ (power I n M) q)
    (hx : moduleHMap (inclusion (I ^ n) M) q x = 0) :
    let _ := powerReesModule ρ I M J hJ q
    powerTransitionComponent ρ I M q hbd (p • (DirectSum.lof R ℕ _ n x)) = 0 := by
  let _ := powerReesModule ρ I M J hJ q
  dsimp only
  obtain ⟨p, rfl⟩ := Rees.sumRingHom_surjective J p
  induction p using DirectSum.induction_on with
  | zero => rw [map_zero, zero_smul, map_zero]
  | add p t hp ht => rw [map_add, add_smul, map_add, hp, ht, add_zero]
  | of a r =>
    rw [Rees.sumRingHom_of]
    exact powerTransitionComponent_monomial_kernel ρ I M J hJ q b d n hbd hd a r x hx

end FLT.Mazur.IdealAdicQuotient

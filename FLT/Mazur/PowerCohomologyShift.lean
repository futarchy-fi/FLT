/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PowerCohomologyScalarMaps

/-!
# Homogeneous endomorphisms of the full power cohomology sum

Take cohomology of the actual scalar lifts and retain their shifted degrees.
The unit and multiplication laws follow from sheaf-level identities, without
using injectivity of maps on higher cohomology.
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

/-- Homogeneous multiplication shifts the full original cohomology sum. -/
def powerShift (a : ℕ) (r : ↥(J ^ a)) : Module.End R (PowerCohomologySum ρ I M q) :=
  DirectSum.toModule R ℕ _ (fun n ↦ (DirectSum.lof R ℕ _ (a + n)).comp
    ((moduleRingHFunctor ρ q).map (powerScalarMap ρ I M J hJ a n r)).hom)

/-- The shift on a single summand is cohomology of the original scalar lift. -/
lemma powerShift_of (a n : ℕ) (r : ↥(J ^ a)) (x : ModuleRingH ρ (power I n M) q) :
    powerShift ρ I M J hJ q a r (DirectSum.lof R ℕ _ n x) =
      DirectSum.lof R ℕ _ (a + n)
        (((moduleRingHFunctor ρ q).map (powerScalarMap ρ I M J hJ a n r)).hom x) := by
  simp only [powerShift, DirectSum.toModule_lof, LinearMap.comp_apply]
  rfl

/-- Equality transport disappears when a class is placed in the full direct sum. -/
lemma powerCohomology_transport {a b : ℕ} (h : a = b)
    (x : ModuleRingH ρ (power I a M) q) :
    DirectSum.lof R ℕ (fun n ↦ ModuleRingH ρ (power I n M) q) b
      (((moduleRingHFunctor ρ q).map
        (powerReindex I M h)).hom x) =
      DirectSum.lof R ℕ _ a x := by
  subst b
  rw [powerReindex_refl, (moduleRingHFunctor ρ q).map_id]
  rfl

/-- Homogeneous coefficient addition gives addition of endomorphisms. -/
lemma powerShift_add (a : ℕ) (r s : ↥(J ^ a)) :
    powerShift ρ I M J hJ q a (r + s) =
      powerShift ρ I M J hJ q a r + powerShift ρ I M J hJ q a s := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.add_apply, powerShift_of,
    powerScalarMap_add, Functor.map_add, ModuleCat.hom_add, map_add]

/-- The homogeneous unit acts as the identity on all original cohomology classes. -/
lemma powerShift_one : powerShift ρ I M J hJ q 0 ⟨1, by simp⟩ = 1 := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro x
  change powerShift ρ I M J hJ q 0 _ (DirectSum.lof R ℕ _ n x) = _
  rw [powerShift_of, powerScalarMap_one, powerCohomology_transport]
  rfl

/-- Homogeneous multiplication composes the constructed endomorphisms. -/
lemma powerShift_mul (a b : ℕ) (r : ↥(J ^ a)) (s : ↥(J ^ b)) :
    powerShift ρ I M J hJ q (a + b)
        ⟨r * s, by simpa only [pow_add] using Ideal.mul_mem_mul r.property s.property⟩ =
      powerShift ρ I M J hJ q a r * powerShift ρ I M J hJ q b s := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro x
  change powerShift ρ I M J hJ q (a + b) _ (DirectSum.lof R ℕ _ n x) =
    powerShift ρ I M J hJ q a r
      (powerShift ρ I M J hJ q b s (DirectSum.lof R ℕ _ n x))
  rw [powerShift_of, powerShift_of, powerShift_of]
  have h := congrArg (fun g ↦ ((moduleRingHFunctor ρ q).map g).hom x)
    (powerScalarMap_mul ρ I M J hJ a b n r s)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h, powerCohomology_transport]

end FLT.Mazur.IdealAdicQuotient

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointIdentityNoetherian
public import FLT.Mazur.FiniteCartierLocalizedComparison

/-!
# The actual finite identity comparison over target primes

At every prime of the original finite chart containing the identity
parameter, the original ring map becomes bijective after base localization.
In particular this applies at the image of the complete base's closed point.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteCartierComparison

/-- A principal augmentation parameter belongs to every prime pulled back from the marking. -/
theorem parameter_mem_comap_of_kernel {R B : Type*} [CommRing R] [CommRing B]
    (ε : R →+* B) (t : R) (hker : RingHom.ker ε = Ideal.span {t}) (p : Ideal B) :
    t ∈ p.comap ε := by
  apply Ideal.ker_le_comap ε
  rw [hker]
  exact Ideal.mem_span_singleton_self t

end FLT.Mazur.FiniteCartierComparison

namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart FiniteCartierComparison
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointIdentityAffineOpen completePointToOrigin completePointOriginOpen
  completePointIdentityAffineSourceMarking completePointIdentityAffineTargetMarking
  completePointWeierstrassCurve

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S₀" => Spec (CommRingCat.of (PowerSeries K))
local notation "q" => completePointToOrigin K n h i
local notation "U" => completePointIdentityAffineOpen K n h i
local notation "T" => Scheme.Opens.toScheme (U)
local notation "Z" => Scheme.Opens.toScheme ((q) ⁻¹ᵁ (U))
local notation "f" => completePointIdentityAffineMap K n h i
local notation "t" => completePointIdentityAffineParameter K n h i
local notation "mT" => completePointIdentityAffineTargetMarking K n h i

/-- The actual target prime obtained from the closed point of the original complete base. -/
def completePointIdentityAffineClosedPrime : PrimeSpectrum Γ(T, ⊤) :=
  (U).toScheme.toSpecΓ ((mT) (IsLocalRing.closedPoint (PowerSeries K)))

/-- The target prime retains the original marking map on global sections. -/
theorem completePointIdentityAffineClosedPrime_eq_comap :
    completePointIdentityAffineClosedPrime K n h i =
      PrimeSpectrum.comap (mT).appTop.hom
        ((S₀).toSpecΓ (IsLocalRing.closedPoint (PowerSeries K))) := by
  exact congrArg (fun g : S₀ ⟶ Spec (.of Γ(T, ⊤)) =>
    g (IsLocalRing.closedPoint (PowerSeries K))) (Scheme.toSpecΓ_naturality (mT))

/-- The original Cartier parameter lies in the prime of the marked closed point. -/
theorem completePointIdentityAffineParameter_mem_closedPrime :
    (t) ∈ (completePointIdentityAffineClosedPrime K n h i).asIdeal := by
  rw [completePointIdentityAffineClosedPrime_eq_comap]
  exact parameter_mem_comap_of_kernel (mT).appTop.hom (t)
    (completePointIdentityAffineTarget_kernel K n h i) _

/-- Localize the entire finite source algebra over any target prime on the original marking. -/
theorem completePointIdentityAffine_atPrime_bijective (p : Ideal Γ(T, ⊤)) [p.IsPrime]
    (hp : (t) ∈ p) :
    let _ := (f).appTop.hom.toAlgebra
    Function.Bijective (algebraMap (Localization.AtPrime p)
      (Localization (Algebra.algebraMapSubmonoid Γ(Z, ⊤) p.primeCompl))) := by
  let _ := (f).appTop.hom.toAlgebra
  let _ := completePointIdentityAffine_isNoetherianRing K n h i
  let _ : Module.Finite Γ(T, ⊤) Γ(Z, ⊤) := completePointIdentityAffine_ringMap_finite K n h i
  apply atPrime_bijective_of_parameterQuotientMap p (t) hp
  · exact isRegular_iff_mem_nonZeroDivisors.mp
      (completePointIdentityAffine_ringMap_parameter_regular K n h i)
  · exact completePointIdentityAffine_quotient_bijective K n h i

/-- The actual original finite comparison is invertible over the marked closed target point. -/
theorem completePointIdentityAffine_closedPrime_bijective :
    let _ := (f).appTop.hom.toAlgebra
    let p := (completePointIdentityAffineClosedPrime K n h i).asIdeal
    Function.Bijective (algebraMap (Localization.AtPrime p)
      (Localization (Algebra.algebraMapSubmonoid Γ(Z, ⊤) p.primeCompl))) :=
  completePointIdentityAffine_atPrime_bijective K n h i _
    (completePointIdentityAffineParameter_mem_closedPrime K n h i)

end FLT.Mazur.PolygonInfinitesimalStages

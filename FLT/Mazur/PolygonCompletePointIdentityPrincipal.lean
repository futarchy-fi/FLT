/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointIdentityLocalIso
public import FLT.Mazur.FiniteCartierIsomorphismNeighborhood

/-!
# Spreading the actual identity comparison along the entire marking

The algebra inverse at the marked closed point spreads to one principal
affine neighborhood. Specialization on the local complete base proves
that this same neighborhood contains the image of every marking point.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
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

/-- The inverse spreads to an actual principal ring neighborhood of the marked closed point. -/
theorem completePointIdentityAffine_exists_principal_bijective :
    let _ := (f).appTop.hom.toAlgebra
    ∃ r : Γ(T, ⊤), r ∉ (completePointIdentityAffineClosedPrime K n h i).asIdeal ∧
      Function.Bijective (algebraMap (Localization.Away r)
        (Localization (Algebra.algebraMapSubmonoid Γ(Z, ⊤) (.powers r)))) := by
  let _ := (f).appTop.hom.toAlgebra
  let _ := completePointIdentityAffine_isNoetherianRing K n h i
  let _ : Module.Finite Γ(T, ⊤) Γ(Z, ⊤) := completePointIdentityAffine_ringMap_finite K n h i
  apply exists_notMem_bijective_of_parameterQuotientMap _ (t)
    (completePointIdentityAffineParameter_mem_closedPrime K n h i)
  · exact isRegular_iff_mem_nonZeroDivisors.mp
      (completePointIdentityAffine_ringMap_parameter_regular K n h i)
  · exact completePointIdentityAffine_quotient_bijective K n h i

/-- Every principal neighborhood of this closed image contains the whole original marking. -/
theorem completePointIdentityAffine_marking_mem_principal (r : Γ(T, ⊤))
    (hr : r ∉ (completePointIdentityAffineClosedPrime K n h i).asIdeal)
    (x : S₀) : (U).toScheme.toSpecΓ ((mT) x) ∈ PrimeSpectrum.basicOpen r := by
  have hs := (IsLocalRing.specializes_closedPoint x).map
    ((mT) ≫ (U).toScheme.toSpecΓ).continuous
  exact hs.mem_open (PrimeSpectrum.basicOpen r).isOpen hr

end FLT.Mazur.PolygonInfinitesimalStages

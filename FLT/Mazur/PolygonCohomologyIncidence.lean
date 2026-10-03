/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonHZeroIncidence
public import FLT.Mazur.PolygonNormalizationHOne
public import FLT.Mazur.PolygonNormalizationExact
public import FLT.Mazur.PolygonIncidenceQuotient
/-!
# The H1 incidence quotient of a polygon

The actual normalization long exact sequence and H8 vanishing identify H1
with the cokernel of the proved cyclic incidence map.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.PolygonCohomologyIncidence
open FCurve PolygonPinching PolygonStructureInclusion PolygonBranchDifferenceSheaf
open PolygonNormalizationHZero
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
local notation "S" => PolygonNormalizationComplex.complex K n hn p q h
/-- The actual additive normalization sequence is short exact. -/
theorem abelian_shortExact : (moduleAbelianComplex S).ShortExact :=
  PolygonNormalizationExact.abelianSheaf_shortExact K n hn p q h
/-- The H5 connecting map in the proved node coordinates. -/
def connecting : (Fin n → K) →ₗ[K] H1 C.hom :=
  (moduleScalarHUnitEquiv C.hom 1).toLinearMap.comp
    ((moduleScalarHConnecting S (abelian_shortExact K n hn p q h) C.hom 0).comp
      (nodeEquiv K n q).symm.toLinearMap)
/-- The coordinate definition of the connecting map. -/
theorem connecting_apply (v : Fin n → K) : connecting K n hn p q h v =
    moduleScalarHUnitEquiv C.hom 1
      (moduleScalarHConnecting S (abelian_shortExact K n hn p q h) C.hom 0
        ((nodeEquiv K n q).symm v)) := rfl
/-- Normalization H1 vanishing makes the connecting map surjective. -/
theorem connecting_surjective : Function.Surjective (connecting K n hn p q h) := by
  intro y
  let y' := (moduleScalarHUnitEquiv C.hom 1).symm y
  have hz₂ : Subsingleton (ModuleScalarH C.hom (S).X₂ (0 + 1)) :=
    PolygonNormalizationHOne.normalization_h1 K n hn p q h
  have he := moduleScalarH_exact₁ S (abelian_shortExact K n hn p q h) C.hom 0
  obtain ⟨z, hz⟩ := (he y').mp (Subsingleton.elim _ _)
  refine ⟨nodeEquiv K n q z, ?_⟩
  rw [connecting_apply, LinearEquiv.symm_apply_apply, hz]
  exact (moduleScalarHUnitEquiv C.hom 1).apply_symm_apply y
/-- The connecting kernel is exactly the image of cyclic incidence. -/
theorem connecting_ker : LinearMap.ker (connecting K n hn p q h) =
    LinearMap.range (PolygonIncidence.difference K hn) := by
  ext v
  have he := moduleScalarH_exact₃ S (abelian_shortExact K n hn p q h) C.hom 0
  constructor
  · intro hv
    change connecting K n hn p q h v = 0 at hv
    have hz : moduleScalarHConnecting S (abelian_shortExact K n hn p q h) C.hom 0
        ((nodeEquiv K n q).symm v) = 0 := by
      apply (moduleScalarHUnitEquiv C.hom 1).injective
      simpa only [connecting_apply, map_zero] using hv
    obtain ⟨x, hx⟩ := (he _).mp hz
    refine ⟨normalizationEquiv K n p x, ?_⟩
    rw [← difference_coordinates K n hn p q h x]
    exact (congrArg (nodeEquiv K n q) hx).trans ((nodeEquiv K n q).apply_symm_apply v)
  · rintro ⟨v, rfl⟩
    let x := (normalizationEquiv K n p).symm v
    have hx := difference_coordinates K n hn p q h x
    have hz : moduleScalarHConnecting S (abelian_shortExact K n hn p q h) C.hom 0
        (moduleScalarHMap C.hom (difference K n hn p q h) 0 x) = 0 :=
      (he _).mpr ⟨x, rfl⟩
    change connecting K n hn p q h (PolygonIncidence.difference K hn v) = 0
    rw [← (normalizationEquiv K n p).apply_symm_apply v, ← hx]
    rw [connecting_apply, LinearEquiv.symm_apply_apply, hz, map_zero]
/-- The actual H1 is the cyclic incidence cokernel over the base field. -/
def h1Incidence : H1 C.hom ≃ₗ[K]
    ((Fin n → K) ⧸ LinearMap.range (PolygonIncidence.difference K hn)) :=
  ((Submodule.quotEquivOfEq _ _ (connecting_ker K n hn p q h).symm).trans
    ((connecting K n hn p q h).quotKerEquivOfSurjective
      (connecting_surjective K n hn p q h))).symm

include h in
/-- The actual polygon H1 has dimension one in every characteristic. -/
theorem h1_finrank : Module.finrank K (H1 C.hom) = 1 := by
  exact LinearEquiv.finrank_eq (h1Incidence K n hn p q h) |>.trans
    (PolygonIncidence.finrank_cokernel K hn)
end FLT.Mazur.PolygonCohomologyIncidence

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PrincipalFiberFreeness
public import FLT.GroupScheme.RaynaudQuotientSpecialFiber
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Relative flatness from a free special fibre

Apply principal-fibre freeness lifting to finite algebras over a noetherian
local domain. For contracted quotient coordinates over the three-adic
integers, this leaves only the special-fibre freeness hypothesis. The
Hopf-subalgebra freeness theorem over a field is not proved here.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Module
variable {R B A : Type*} [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra R A] [Algebra B A] [IsScalarTower R B A]

/-- A nonunit of a local ring maps into the Jacobson radical of every finite
algebra over that ring. -/
theorem Algebra.map_mem_jacobson_of_not_isUnit_of_finite
    [IsLocalRing R] [Module.Finite R B] (r : R) (hr : ¬ IsUnit r) :
    algebraMap R B r ∈ (⊥ : Ideal B).jacobson := by
  apply Submodule.mem_sInf.mpr
  intro m hm
  let : Ideal.IsMaximal m := hm.2
  have hmR := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) m
  change r ∈ Ideal.under R m
  rw [IsLocalRing.eq_maximalIdeal hmR]
  exact hr

/-- For finite algebras over a noetherian local domain, a free principal
special fibre lifts to relative freeness when the source is torsion-free
over the original base. No relative flatness is assumed. -/
theorem Module.free_of_free_principal_fiber [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]
    [Module.Finite R B] [Module.Finite R A] [Module.IsTorsionFree R A]
    [Nontrivial B] (r : R) (hr : ¬ IsUnit r) (hr0 : r ≠ 0)
    [Module.Free (B ⧸ Ideal.span {algebraMap R B r})
      ((B ⧸ Ideal.span {algebraMap R B r}) ⊗[B] A)] : Module.Free B A := by
  let : IsNoetherianRing B := IsNoetherianRing.of_finite R B
  let : Module.Finite B A := Module.Finite.of_restrictScalars_finite R B A
  let : Module.FinitePresentation B A := Module.finitePresentation_of_finite B A
  apply Module.free_of_free_quotient_of_smul_regular (algebraMap R B r)
  · exact Algebra.map_mem_jacobson_of_not_isUnit_of_finite r hr
  · intro x y hxy
    apply (IsSMulRegular.of_ne_zero (M := A) hr0)
    simpa only [algebraMap_smul] using hxy

namespace ThreeAdicPlan


/-- The base change of a contracted quotient inclusion is an injective
bialgebra map, including after passage to a residue field. -/
theorem GenericGaloisHom.quotientInclusion_baseChange_injective
    {R K : Type} [CommRing R] [Field K] [Algebra R K]
    [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]
    {X Y : FF R K} (q : GenericGaloisHom X Y)
    (S : Type) [CommRing S] [Algebra R S] :
    Function.Injective
      (Bialgebra.TensorProduct.map (BialgHom.id S S) q.quotientInclusion) :=
  q.quotientInclusion_lTensor_injective S

variable {X Y : FF ℤ_[3] ℚ_[3]}

/-- Relative flatness of a contracted three-adic quotient follows from
freeness of its special fibre. The special-fibre freeness input is the
remaining Hopf-subalgebra theorem over the residue field. -/
theorem GenericGaloisHom.quotientCoordinates_flat_of_free_mod_three
    (q : GenericGaloisHom X Y)
    [Module.Free (q.quotientCoordinates ⧸ Ideal.span {(3 : q.quotientCoordinates)})
      ((q.quotientCoordinates ⧸ Ideal.span {(3 : q.quotientCoordinates)}) ⊗[q.quotientCoordinates]
        X.CoordinateRing)] : Module.Flat q.quotientCoordinates X.CoordinateRing := by
  let : Nontrivial q.quotientCoordinates :=
    (Bialgebra.counitAlgHom ℤ_[3] q.quotientCoordinates).toRingHom.domain_nontrivial
  have hf : Module.Free
      (q.quotientCoordinates ⧸ Ideal.span {algebraMap ℤ_[3] q.quotientCoordinates 3})
      ((q.quotientCoordinates ⧸ Ideal.span {algebraMap ℤ_[3] q.quotientCoordinates 3})
        ⊗[q.quotientCoordinates] X.CoordinateRing) := by
    have hmap : algebraMap ℤ_[3] q.quotientCoordinates 3 =
        (3 : q.quotientCoordinates) := map_ofNat _ 3
    rw [hmap]
    infer_instance
  let : Module.Free q.quotientCoordinates X.CoordinateRing :=
    Module.free_of_free_principal_fiber (R := ℤ_[3]) (3 : ℤ_[3])
      (by
        have h := PadicInt.norm_p (p := 3)
        norm_num at h
        rw [PadicInt.not_isUnit_iff, h]
        norm_num)
      (by norm_num)
  infer_instance
end ThreeAdicPlan

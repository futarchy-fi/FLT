/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeComponentLabel
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Realizing an abstract valuation ring inside its fraction field

The canonical valuation gives an actual valuation subring, with an equivalence
that preserves the uniformizer, all maximal-ideal powers, and split nodal depth.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable (R K : Type*) [CommRing R] [IsDomain R] [ValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The image of an abstract valuation ring in its fraction field. -/
noncomputable def fractionValuationSubring : ValuationSubring K :=
  (ValuationRing.valuation R K).valuationSubring

/-- The abstract valuation ring and its actual subring of the fraction field agree. -/
noncomputable def fractionValuationEquiv : R ≃+* fractionValuationSubring R K :=
  ValuationRing.equivInteger R K

/-- The realization map is the original fraction-field embedding. -/
@[simp] theorem fractionValuationEquiv_coe (x : R) :
    (fractionValuationEquiv R K x : K) = algebraMap R K x := rfl

/-- Discreteness is retained by the realization as a valuation subring. -/
theorem fractionValuationSubring_isDiscreteValuationRing [IsDiscreteValuationRing R] :
    IsDiscreteValuationRing (fractionValuationSubring R K) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (fractionValuationEquiv R K)

variable {R K}

/-- Ring equivalences preserve and reflect every maximal-ideal power. -/
theorem ringEquiv_mem_maximalIdeal_pow_iff {S T : Type*}
    [CommRing S] [CommRing T] [IsLocalRing S] [IsLocalRing T]
    (e : S ≃+* T) (x : S) (n : ℕ) :
    e x ∈ maximalIdeal T ^ n ↔ x ∈ maximalIdeal S ^ n := by
  rw [← map_ringEquiv_maximalIdeal e, ← Ideal.map_pow]
  exact Ideal.apply_mem_of_equiv_iff

/-- Split finite-depth coefficient conditions transport along a ring equivalence. -/
theorem SplitNodeDepth.ringEquiv {S T : Type*}
    [CommRing S] [CommRing T] [IsLocalRing S] [IsLocalRing T]
    {W : WeierstrassCurve S} {π : S} {n : ℕ}
    (D : SplitNodeDepth W π n) (e : S ≃+* T) :
    SplitNodeDepth (W.map e.toRingHom) (e π) n := by
  have hm := ringEquiv_mem_maximalIdeal_pow_iff e
  refine ⟨D.depth_pos, fun h => D.uniformizer_ne_zero (e.injective (by simpa using h)),
    ?_, D.a₁_unit.map e.toRingHom, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_ringEquiv_maximalIdeal e, D.maximalIdeal_eq,
      Ideal.map_span, Set.image_singleton]
  · exact (by simpa using (hm W.a₂ 1).mpr (by simpa using D.a₂_mem))
  · exact (hm _ _).mpr D.a₃_mem
  · exact (hm _ _).mpr D.a₄_mem
  · exact (hm _ _).mpr D.a₆_mem
  · exact fun h => D.a₆_not_mem ((hm _ _).mp h)

variable {A : Type*} [CommRing A] [Algebra A R] [Algebra A K] [IsScalarTower A R K]

/-- The original base ring maps locally into the realized valuation subring. -/
noncomputable def fractionValuationBaseMap : A →+* fractionValuationSubring R K :=
  (fractionValuationEquiv R K).toRingHom.comp (algebraMap A R)

instance [IsLocalHom (algebraMap A R)] :
    IsLocalHom (fractionValuationBaseMap (A := A) (R := R) (K := K)) :=
by
  constructor
  intro x hx
  have h := hx.map (fractionValuationEquiv R K).symm
  change IsUnit ((fractionValuationEquiv R K).symm
    (fractionValuationEquiv R K (algebraMap A R x))) at h
  rw [RingEquiv.symm_apply_apply] at h
  exact IsLocalHom.map_nonunit (f := (algebraMap A R : A →+* R)) x h

/-- The local base map commutes with the given fraction-field tower. -/
theorem fractionValuationBaseMap_coe (a : A) :
    (fractionValuationBaseMap (R := R) (K := K) a : K) = algebraMap A K a :=
  (IsScalarTower.algebraMap_apply A R K a).symm

end FLT.Mazur

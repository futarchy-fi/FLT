/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ResiduePolynomialLift
public import FLT.Mazur.EtaleSimpleRootCoordinates
public import Mathlib.FieldTheory.Separable

/-!
# Constructed étale coefficients for separable residue coordinates

A finite tuple of elements separable over a base residue field lifts to an
actual étale algebra over the original ring. Minimal polynomial coefficients
are first lifted over one principal open; adjoining their simple roots gives
the required coefficient extension, without a supplied étale neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial
namespace FLT.Mazur.EtaleSeparableResidueCoordinates
variable {R k K : Type} [CommRing R] [Field k] [Field K] [Algebra k K]

/-- Construct an étale coefficient ring carrying any finite separable residue-coordinate tuple. -/
theorem exists_coordinates (φ : R →+* k) (hφ : φ.SurjectiveOnStalks)
    {n : ℕ} (v : Fin n → K) (hv : ∀ i, IsSeparable k (v i)) :
    ∃ (A : CommRingCat.{0}) (a : R →+* A) (q : A →+* K) (x : Fin n → A),
      a.Etale ∧ q.comp a = (algebraMap k K).comp φ ∧ ∀ i, q (x i) = v i := by
  obtain ⟨r, _, ψ, hψ, p, hp⟩ := ResiduePolynomialLift.exists_monic_family φ hφ
    (fun i ↦ minpoly k (v i)) (fun i ↦ minpoly.monic (hv i).isIntegral)
  let χ := (algebraMap k K).comp ψ
  have hroot (i : Fin n) : (p i).eval₂ χ (v i) = 0 := by
    rw [← eval₂_map, (hp i).1]
    exact minpoly.aeval k (v i)
  have hder (i : Fin n) : (p i).derivative.eval₂ χ (v i) ≠ 0 := by
    rw [← eval₂_map, ← derivative_map, (hp i).1]
    exact (hv i).aeval_derivative_ne_zero (minpoly.aeval k (v i))
  obtain ⟨A, a, q, x, ha, hq, hx⟩ := EtaleSimpleRootCoordinates.exists_family χ p
    (fun i ↦ (hp i).2.2) v hroot hder
  have hr : (algebraMap R (Localization.Away r)).Etale :=
    RingHom.etale_algebraMap.mpr inferInstance
  refine ⟨A, a.comp (algebraMap R (Localization.Away r)), q, x,
    RingHom.Etale.stableUnderComposition _ _ hr ha, ?_, hx⟩
  rw [← RingHom.comp_assoc, hq]
  exact congrArg (RingHom.comp (algebraMap k K)) hψ

/-- In a separable field extension, every finite tuple admits the constructed coefficient lift. -/
theorem exists_coordinates_of_isSeparable [Algebra.IsSeparable k K]
    (φ : R →+* k) (hφ : φ.SurjectiveOnStalks) {n : ℕ} (v : Fin n → K) :
    ∃ (A : CommRingCat.{0}) (a : R →+* A) (q : A →+* K) (x : Fin n → A),
      a.Etale ∧ q.comp a = (algebraMap k K).comp φ ∧ ∀ i, q (x i) = v i :=
  exists_coordinates φ hφ v (fun i ↦ Algebra.IsSeparable.isSeparable k (v i))

end FLT.Mazur.EtaleSeparableResidueCoordinates

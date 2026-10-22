/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Finite equation witnesses for flat ring maps

The coefficients and generators of a trivial relation are explicit finite
families. Their equations survive every commutative square of ring maps.
This transports individual flatness tests, not flatness of the new ring map.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace FLT.Mazur.RingFlatRelation
variable {R S R' S' : Type*} [CommRing R] [CommRing S]
  [CommRing R'] [CommRing S'] {ι : Type*} [Fintype ι]

/-- The finite matrix and generators witnessing a trivial ring relation. -/
def Trivial (φ : R →+* S) (f : ι → R) (x : ι → S) : Prop :=
  ∃ (k : ℕ) (a : ι → Fin k → R) (y : Fin k → S),
    (∀ i, x i = ∑ j, φ (a i j) * y j) ∧ ∀ j, ∑ i, f i * a i j = 0

/-- The explicit ring equations are exactly the module equational criterion. -/
theorem trivial_iff_module (φ : R →+* S) (f : ι → R) (x : ι → S) :
    Trivial φ f x ↔ @Module.IsTrivialRelation R S _ _ φ.toAlgebra.toModule ι _ f x :=
  Iff.rfl

/-- A flat original algebra supplies finite witnesses for each actual relation. -/
theorem trivial_of_flat (φ : R →+* S) (hφ : φ.Flat) (f : ι → R) (x : ι → S)
    (h : ∑ i, φ (f i) * x i = 0) : Trivial φ f x := by
  let _ := φ.toAlgebra
  let _ : Module.Flat R S := hφ
  exact Module.Flat.isTrivialRelation_of_sum_smul_eq_zero h

/-- Witness equations remain valid under a commutative square, including nonflat changes. -/
theorem trivial_map (φ : R →+* S) (ψ : R' →+* S')
    (r : R →+* R') (s : S →+* S') (he : s.comp φ = ψ.comp r)
    (f : ι → R) (x : ι → S) (h : Trivial φ f x) :
    Trivial ψ (fun i ↦ r (f i)) (fun i ↦ s (x i)) := by
  obtain ⟨k, a, y, hx, ha⟩ := h
  refine ⟨k, fun i j ↦ r (a i j), fun j ↦ s (y j), fun i ↦ ?_, fun j ↦ ?_⟩
  · have hs (z : R) : s (φ z) = ψ (r z) := RingHom.congr_fun he z
    simpa only [map_sum, map_mul, hs] using congrArg s (hx i)
  · simpa only [map_sum, map_mul, map_zero] using congrArg r (ha j)

/-- A finite witness entails the original relation, with no flatness premise. -/
theorem sum_eq_zero (φ : R →+* S) (f : ι → R) (x : ι → S)
    (h : Trivial φ f x) : ∑ i, φ (f i) * x i = 0 := by
  let _ := φ.toAlgebra
  exact Module.sum_smul_eq_zero_of_isTrivialRelation h

end FLT.Mazur.RingFlatRelation

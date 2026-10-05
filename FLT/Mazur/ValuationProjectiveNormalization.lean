/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Data.Finset.Max

/-!
# Primitive projective coordinates over a valuation ring

Nonzero finite vectors can be scaled to integral vectors with a unit coordinate.
For such primitive vectors, equivalence over the fraction field already comes
from an integral unit. Consequently reduction of their projective class is
independent of the primitive representative.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve.Projective

variable {K : Type*} [Field K] (A : ValuationSubring K)

/-- An integral coordinate vector is primitive if one coordinate is a unit. -/
def UnitCoordinate {ι : Type*} (v : ι → A) : Prop := ∃ i, IsUnit (v i)

/-- Normalize a nonzero finite vector by a coordinate of largest valuation. -/
theorem exists_primitive_coordinates {ι : Type*} [Finite ι]
    (v : ι → K) (hv : ∃ i, v i ≠ 0) :
    ∃ (w : ι → A) (u : Kˣ), UnitCoordinate A w ∧
      (fun i => (w i : K)) = u • v := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨j, hj⟩ := hv
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => A.valuation (v i)) ⟨j, Finset.mem_univ j⟩
  have hi0 : v i ≠ 0 := by
    intro h
    have hh := hi j (Finset.mem_univ j)
    rw [h, map_zero] at hh
    exact hj ((map_eq_zero A.valuation).mp (le_antisymm hh zero_le))
  have hm (j) : v j / v i ∈ A := by
    rw [← A.valuation_le_one_iff, map_div₀, div_le_one₀]
    · exact hi j (Finset.mem_univ j)
    · exact pos_iff_ne_zero.mpr ((map_ne_zero A.valuation).mpr hi0)
  refine ⟨fun j => ⟨v j / v i, hm j⟩, (Units.mk0 (v i) hi0)⁻¹, ?_, ?_⟩
  · refine ⟨i, ?_⟩
    have he : (⟨v i / v i, hm i⟩ : A) = 1 := Subtype.ext (div_self hi0)
    change IsUnit (⟨v i / v i, hm i⟩ : A)
    rw [he]
    exact isUnit_one
  · funext j
    simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul, Units.val_inv_eq_inv_val,
      Units.val_mk0, div_eq_mul_inv, mul_comm]

/-- A scalar relating primitive integral vectors is integral. -/
theorem scalar_mem_of_primitive {ι : Type*} {v w : ι → A}
    (hw : UnitCoordinate A w) {u : K}
    (h : ∀ i, (v i : K) = u * (w i : K)) : u ∈ A := by
  obtain ⟨i, hi⟩ := hw
  have he : u = ((v i * ↑hi.unit⁻¹ : A) : K) := by
    change u = (v i : K) * ((hi.unit⁻¹ : Aˣ) : A)
    have hiu : (((hi.unit⁻¹ : Aˣ) : A) : K) = (w i : K)⁻¹ := by
      exact map_units_inv (algebraMap A K) hi.unit
    rw [hiu, h i, mul_inv_cancel_right₀ (show (w i : K) ≠ 0 from
      fun hh => hi.ne_zero (Subtype.ext hh))]
  rw [he]
  exact Subtype.mem _

/-- Generic equivalence of primitive vectors descends to integral equivalence. -/
theorem primitive_equiv_of_generic_equiv {v w : Fin 3 → A}
    (hv : UnitCoordinate A v) (hw : UnitCoordinate A w)
    (h : (fun i => (v i : K)) ≈ (fun i => (w i : K))) : v ≈ w := by
  obtain ⟨u, hu⟩ := h
  have he (i) : (v i : K) = (u : K) * (w i : K) := by
    exact (congrFun hu i).symm
  have hm := scalar_mem_of_primitive A hw he
  have hinv := scalar_mem_of_primitive A (v := w) (w := v) hv (u := (↑u : K)⁻¹) (by
    intro i
    rw [he i, inv_mul_cancel_left₀ u.ne_zero])
  let a : Aˣ :=
    { val := ⟨u, hm⟩
      inv := ⟨(↑u : K)⁻¹, hinv⟩
      val_inv := Subtype.ext (mul_inv_cancel₀ u.ne_zero)
      inv_val := Subtype.ext (inv_mul_cancel₀ u.ne_zero) }
  refine ⟨a, ?_⟩
  funext i
  apply Subtype.ext
  exact (he i).symm

/-- Reduction respects generic equivalence of primitive integral vectors. -/
theorem residue_equiv_of_generic_equiv {v w : Fin 3 → A}
    (hv : UnitCoordinate A v) (hw : UnitCoordinate A w)
    (h : (fun i => (v i : K)) ≈ (fun i => (w i : K))) :
    (residue A ∘ v) ≈ (residue A ∘ w) := by
  obtain ⟨u, hu⟩ := primitive_equiv_of_generic_equiv A hv hw h
  refine ⟨Units.map (residue A) u, ?_⟩
  funext i
  have hh := congrArg (residue A) (congrFun hu i)
  change residue A (u : A) * residue A (w i) = residue A (v i)
  simpa only [Units.smul_def, Pi.smul_apply, smul_eq_mul, map_mul] using hh

end FLT.Mazur

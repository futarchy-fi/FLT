/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonPolynomialMatching
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# Cubic interpolation with weighted endpoint matching

The two interior coefficients prescribe both branch-linear coefficients freely.
Away from zero, a polynomial supported on one component prescribes any first
jet, including in characteristics two and three. These are polynomial families;
transport to actual divisor-sheaf sections remains a separate proof.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonCubicInterpolation
open Polynomial PolynomialEndpointInterpolation PolygonPolynomialMatching
variable {R ι : Type*} [CommRing R]

/-- The bounded cubic with four prescribed coefficients. -/
def cubic (a b c e : R) : Bounded R 2 :=
  ⟨monomial 0 a + monomial 1 b + monomial 2 c + monomial 3 e,
    (degreeLT R 4).add_mem
      ((degreeLT R 4).add_mem
        ((degreeLT R 4).add_mem (monomial_coe_mem_degreeLT ⟨0, by decide⟩ _)
          (monomial_coe_mem_degreeLT ⟨1, by decide⟩ _))
        (monomial_coe_mem_degreeLT ⟨2, by decide⟩ _))
      (monomial_coe_mem_degreeLT ⟨3, by decide⟩ _)⟩

/-- The constant coefficient of the prescribed cubic. -/
@[simp] theorem cubic_coeff_zero (a b c e : R) : (cubic a b c e).val.coeff 0 = a := by
  simp [cubic, coeff_monomial]

/-- The first branch-linear coefficient of the prescribed cubic. -/
@[simp] theorem cubic_coeff_one (a b c e : R) : (cubic a b c e).val.coeff 1 = b := by
  simp [cubic, coeff_monomial]

/-- The opposite branch-linear coefficient in reversed homogeneous coordinates. -/
@[simp] theorem cubic_coeff_two (a b c e : R) : (cubic a b c e).val.coeff 2 = c := by
  simp [cubic, coeff_monomial]

/-- The highest coefficient of the prescribed cubic. -/
@[simp] theorem cubic_coeff_three (a b c e : R) : (cubic a b c e).val.coeff 3 = e := by
  simp [cubic, coeff_monomial]

/-- A matching cubic family with arbitrary constants and interior coefficients. -/
def lift (neighbor : ι → ι) (weight v b c : ι → R) : matching (fun _ ↦ 2) neighbor weight :=
  ⟨fun i ↦ cubic (v i) (b i) (c i) (weight i * v (neighbor i)), by
    rw [mem_matching]
    intro i
    simp⟩

/-- Both interior coefficients remain free after imposing endpoint matching. -/
theorem prescribed_node_jets (neighbor : ι → ι) (weight v b c : ι → R) :
    ∃ p : matching (fun _ ↦ 2) neighbor weight, ∀ i,
      (p.val i).val.coeff 0 = v i ∧ (p.val i).val.coeff 1 = b i ∧
        (p.val i).val.coeff 2 = c i := by
  exact ⟨lift neighbor weight v b c, fun i ↦ by simp [lift]⟩

variable {K : Type*} [Field K]

/-- A cubic with zero endpoint values and prescribed value and derivative away from zero. -/
def interiorJet (a r s : K) : Bounded K 2 :=
  cubic 0 ((2 * r - a * s) / a) ((a * s - r) / a ^ 2) 0

/-- The interior jet interpolant vanishes at both endpoints. -/
@[simp] theorem interiorJet_endpoints (a r s : K) :
    endpoints 2 (interiorJet a r s) = (0, 0) := by
  ext <;> simp [endpoints, interiorJet]

/-- The interior interpolant has the prescribed value. -/
theorem interiorJet_eval {a : K} (ha : a ≠ 0) (r s : K) :
    (interiorJet a r s).val.eval a = r := by
  simp only [interiorJet, cubic, eval_add, eval_monomial]
  field_simp
  ring

/-- The interior interpolant has the prescribed formal derivative. -/
theorem interiorJet_derivative {a : K} (ha : a ≠ 0) (r s : K) :
    (derivative (interiorJet a r s).val).eval a = s := by
  simp [interiorJet, cubic]
  field_simp
  ring

/-- A polynomial family supported on one component realizes any first jet away from zero. -/
theorem prescribed_interior_jet (neighbor : ι → ι) (weight : ι → K)
    (i : ι) {a : K} (ha : a ≠ 0) (r s : K) :
    ∃ p : matching (fun _ ↦ 2) neighbor weight,
      (p.val i).val.eval a = r ∧ (derivative (p.val i).val).eval a = s ∧
        (∀ j, (p.val j).val.coeff 0 = 0) ∧ (∀ j, j ≠ i → (p.val j).val = 0) := by
  classical
  let b : ι → K := fun j ↦ if j = i then (2 * r - a * s) / a else 0
  let c : ι → K := fun j ↦ if j = i then (a * s - r) / a ^ 2 else 0
  let p := lift neighbor weight 0 b c
  have hi : p.val i = interiorJet a r s := by simp [p, lift, b, c, interiorJet]
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · rw [hi]; exact interiorJet_eval ha r s
  · rw [hi]; exact interiorJet_derivative ha r s
  · intro j; simp [p, lift]
  · intro j hj; simp [p, lift, b, c, hj, cubic]

end FLT.Mazur.PolygonCubicInterpolation

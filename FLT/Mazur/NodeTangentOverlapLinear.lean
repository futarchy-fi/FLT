/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentExtension
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Linear coordinates on the actual quadratic coefficient overlap

Every element of the tangent algebra is linear in its root over the original
ring, without irreducibility or a field hypothesis. Consequently the actual
Cech tensor algebra is linear in the second root over its first projection.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur
open Polynomial
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] [Nontrivial R] (W : WeierstrassCurve R)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "s" => AdjoinRoot.root (nodeTangentPolynomial W)

/-- The monic quadratic gives integral linear coordinates, even for a split algebra. -/
theorem nodeTangentAlgebra_exists_linear (z : S) :
    ∃ b c : R, z = algebraMap R S b * s + algebraMap R S c := by
  let _ : Nontrivial S := (AdjoinRoot.nontrivial_iff_of_monic
    (nodeTangentPolynomial_monic W)).mpr (by rw [nodeTangentPolynomial_degree]; decide)
  let pb := AdjoinRoot.powerBasis' (nodeTangentPolynomial_monic W)
  obtain ⟨f, hf, hz⟩ := pb.exists_eq_aeval z
  have hd : pb.dim = 2 := natDegree_eq_of_degree_eq_some (nodeTangentPolynomial_degree W)
  obtain ⟨b, c, hbc⟩ := exists_eq_X_add_C_of_natDegree_le_one (by omega : f.natDegree ≤ 1)
  refine ⟨b, c, ?_⟩
  rw [hz, hbc]
  simp [pb]

/-- The genuine coefficient overlap has a two-term expression in the second root. -/
theorem nodeTangentOverlap_exists_linear (z : S ⊗[R] S) :
    ∃ b c : S, z = b ⊗ₜ[R] s + c ⊗ₜ[R] (1 : S) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨b, c, rfl⟩ := nodeTangentAlgebra_exists_linear W y
    refine ⟨x * algebraMap R S b, x * algebraMap R S c, ?_⟩
    rw [TensorProduct.tmul_add]
    congr 1
    · rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
        TensorProduct.tmul_smul, mul_smul_comm, mul_one,
        TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    · rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        mul_smul_comm, mul_one,
        TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  | add x y hx hy =>
    obtain ⟨b, c, rfl⟩ := hx
    obtain ⟨d, e, rfl⟩ := hy
    refine ⟨b + d, c + e, ?_⟩
    simp only [TensorProduct.add_tmul]
    abel

end FLT.Mazur

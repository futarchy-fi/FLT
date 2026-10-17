/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteKernelCorrections
public import Mathlib.LinearAlgebra.Pi

/-!
# The linear operator of finite ambient kernel corrections

Although the relation difference is not linear over the ambient source ring,
it is linear over scalars on which the two endpoints agree. The finite ideal
frame then gives a linear operator with finitely many ambient coordinates.
Its range is exactly the image of the entire restriction kernel. This does
not assert that the ambient coordinate modules are finite over the scalars.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteKernelCorrections
variable (R : Type*) [CommRing R] {Q T C : Type*}
  [CommRing Q] [CommRing T] [CommRing C]
  [Algebra R Q] [Algebra R T] [Algebra R C]
  {n : ℕ} (z : Fin n → Q)

/-- Synthesis of an ambient ideal correction, linear over the original scalars. -/
def synthesis : (Fin n → Q) →ₗ[R] Q :=
  (Fintype.linearCombination Q z).restrictScalars R

/-- Evaluation retains the ambient coefficients rather than replacing them by scalar ones. -/
theorem synthesis_apply (u : Fin n → Q) : synthesis R z u = ∑ j, u j * z j := rfl

/-- The difference of the full endpoints applied to the synthesized kernel correction. -/
def operator (p q : Q →ₐ[R] C) : (Fin n → Q) →ₗ[R] C :=
  (p.toLinearMap - q.toLinearMap).comp (synthesis R z)

/-- Both endpoint actions appear in the coordinate formula of the scalar-linear operator. -/
theorem operator_apply (p q : Q →ₐ[R] C) (u : Fin n → Q) :
    operator R z p q u =
      ∑ j, (p (u j) * p (z j) - q (u j) * q (z j)) := by
  change p (∑ j, u j * z j) - q (∑ j, u j * z j) = _
  exact difference_sum z p.toRingHom q.toRingHom u

variable (r : Q →ₐ[R] T)
  (hz : Ideal.span (Set.range z) = RingHom.ker r.toRingHom)
include hz

/-- The finite-coordinate synthesis covers exactly the full scalar-linear restriction kernel. -/
theorem synthesis_range : LinearMap.range (synthesis R z) = LinearMap.ker r.toLinearMap := by
  ext a
  change (∃ u, synthesis R z u = a) ↔ r a = 0
  simp only [synthesis_apply]
  rw [← Ideal.mem_span_range_iff_exists_fun, hz]
  rfl

/-- Finite ambient coordinates recover all kernel corrections, with no smaller correction image. -/
theorem operator_range (p q : Q →ₐ[R] C) :
    LinearMap.range (operator R z p q) =
      Submodule.map (p.toLinearMap - q.toLinearMap) (LinearMap.ker r.toLinearMap) := by
  rw [operator, LinearMap.range_comp, synthesis_range R z r hz]

end FLT.Mazur.FiniteKernelCorrections

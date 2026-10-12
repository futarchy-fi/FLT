/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SplitEvaluationBaseChange
public import Mathlib.RingTheory.Grassmannian

/-!
# Grassmannian scalar extension through an ambient comparison

Extend a quotient Grassmannian point and transport it along any specified
linear comparison of the extended ambient module. The underlying submodule is
the image of the tensor-extended original relations.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.HilbertChart
variable {S : Type*} [CommRing S] {M : Type*} [AddCommGroup M] [Module S M]
  (T : Type*) [CommRing T] [Algebra S T]
  {P : Type*} [AddCommGroup P] [Module T P] {d : ℕ}
  (N : Module.Grassmannian S M d) (e : T ⊗[S] M ≃ₗ[T] P)

/-- Extend the actual quotient map and use the given ambient comparison. -/
def grassmannianExtendedEvaluation : P →ₗ[T] T ⊗[S] (M ⧸ N.toSubmodule) :=
  (N.toSubmodule.mkQ.baseChange T).comp e.symm.toLinearMap

/-- The extended quotient map remains surjective over any coefficient algebra. -/
theorem grassmannianExtendedEvaluation_surjective :
    Function.Surjective (grassmannianExtendedEvaluation T N e) :=
  (LinearMap.baseChange_surjective T N.toSubmodule.mkQ_surjective).comp e.symm.surjective

/-- Scalar extension of quotient Grassmannian points, in chosen ambient coordinates. -/
def grassmannianScalarExtension : Module.Grassmannian T P d := by
  let q := grassmannianExtendedEvaluation T N e
  let c := q.quotKerEquivOfSurjective (grassmannianExtendedEvaluation_surjective T N e)
  refine { toSubmodule := q.ker
           finite_quotient := Module.Finite.equiv c.symm
           projective_quotient := Module.Projective.of_equiv c.symm
           rankAtStalk_eq := ?_ }
  intro p
  calc
    _ = Module.rankAtStalk (T ⊗[S] (M ⧸ N.toSubmodule)) p :=
      congrFun (Module.rankAtStalk_eq_of_equiv c) p
    _ = Module.rankAtStalk (M ⧸ N.toSubmodule) (p.comap (algebraMap S T)) :=
      Module.rankAtStalk_baseChange _
    _ = d := N.rankAtStalk_eq _

/-- The construction extends exactly the original submodule of relations. -/
theorem grassmannianScalarExtension_submodule :
    (grassmannianScalarExtension T N e).toSubmodule =
      (N.toSubmodule.baseChange T).map e.toLinearMap := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.toSubmodule.mkQ LinearMap.id
    N.toSubmodule.mkQ_surjective
  have hk := Approximation.splitEvaluation_baseChange_kernel N.toSubmodule.mkQ s hs T
  rw [Submodule.ker_mkQ] at hk
  change LinearMap.ker ((N.toSubmodule.mkQ.baseChange T).comp e.symm.toLinearMap) = _
  rw [LinearMap.ker_comp, ← hk, Submodule.map_equiv_eq_comap_symm]

end FLT.Mazur.HilbertChart

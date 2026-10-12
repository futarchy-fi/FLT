/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

import all Mathlib.RingTheory.Grassmannian

public import FLT.Mazur.GrassmannianFunctorLocalizedChart
public import FLT.Mazur.GrassmannianScalarExtension
public import FLT.Mazur.GrassmannianAmbientPointTransport

/-!
# Scalar extension commutes with ambient transport

The quotient comparison transports the entire extended evaluation map. Thus
changing ambient coordinates before coefficient extension preserves every relation.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.HilbertChart
open GrassmannianChart
set_option backward.isDefEq.respectTransparency false
variable {S : Type*} [CommRing S] (T : Type*) [CommRing T] [Algebra S T]
  {M P : Type*} [AddCommGroup M] [Module S M] [AddCommGroup P] [Module S P]
  {Q : Type*} [AddCommGroup Q] [Module T Q] {d : ℕ}

/-- Extending a transported quotient equals extending in the composite ambient coordinates. -/
theorem grassmannianScalarExtension_transport (e : M ≃ₗ[S] P)
    (N : Module.Grassmannian S M d) (f : T ⊗[S] P ≃ₗ[T] Q) :
    grassmannianScalarExtension T (ambientTransportPoint e N) f =
      grassmannianScalarExtension T N ((e.baseChange S T).trans f) := by
  let E := (ambientTransportQuotientEquiv e N).baseChange S T
  have hc : E.toLinearMap.comp
      (grassmannianExtendedEvaluation T (ambientTransportPoint e N) f) =
      grassmannianExtendedEvaluation T N ((e.baseChange S T).trans f) := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := f.surjective x
    induction y using TensorProduct.inductionOn with
    | tmul t p =>
      change E (((ambientTransportPoint e N).toSubmodule.mkQ.baseChange T)
        (f.symm (f (t ⊗ₜ[S] p)))) =
          (N.toSubmodule.mkQ.baseChange T)
            (((e.baseChange S T).trans f).symm (f (t ⊗ₜ[S] p)))
      simp only [E, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul,
        LinearEquiv.baseChange_tmul, LinearEquiv.trans_symm,
        LinearEquiv.trans_apply, ← LinearEquiv.baseChange_symm]
      exact congrArg (fun z ↦ t ⊗ₜ[S] z)
        (LinearMap.congr_fun (ambientTransportQuotientEquiv_mkQ e N) p)
    | add x y hx hy => simp only [map_add, hx, hy]
  apply Module.Grassmannian.ext
  change (grassmannianExtendedEvaluation T (ambientTransportPoint e N) f).ker =
    (grassmannianExtendedEvaluation T N ((e.baseChange S T).trans f)).ker
  rw [← hc, LinearEquiv.ker_comp]

/-- Transporting the extended ambient is composition with that ambient equivalence. -/
theorem ambientTransportPoint_scalarExtension (N : Module.Grassmannian S M d)
    (e : T ⊗[S] M ≃ₗ[T] Q) {V : Type*} [AddCommGroup V] [Module T V]
    (f : Q ≃ₗ[T] V) :
    ambientTransportPoint f (grassmannianScalarExtension T N e) =
      grassmannianScalarExtension T N (e.trans f) := by
  apply Module.Grassmannian.ext
  ext x
  rw [ambientTransportPoint_mem]
  rfl

section Tower
universe u
variable {R A B V : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [AddCommGroup V] [Module R V]

/-- The Grassmannian functor uses precisely the original tensor-extension comparison. -/
theorem grassmannian_map_scalarExtension (N : Module.Grassmannian A (A ⊗[R] V) d) :
    Module.Grassmannian.map (IsScalarTower.toAlgHom R A B) N =
      grassmannianScalarExtension B N (AlgebraTensorModule.cancelBaseChange R A B B V) := by
  apply Module.Grassmannian.ext
  have ha : (IsScalarTower.toAlgHom R A B).toAlgebra = ‹Algebra A B› :=
    Algebra.algebra_ext _ _ fun _ ↦ rfl
  exact (Module.Grassmannian.map_toSubmodule _ N).trans
    (baseChangeMkQ_ker_algebra_congr _ _ ha _ _ N.toSubmodule)

end Tower
end FLT.Mazur.HilbertChart

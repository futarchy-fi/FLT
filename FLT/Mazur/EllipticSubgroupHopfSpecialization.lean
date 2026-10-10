/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupHopfMultiplication
public import FLT.GroupScheme.HopfTestAlgebraPoints

/-!
# Specializing the original subgroup points

Postcomposing integral evaluation with any test algebra gives the actual
specialized section. The recovered Hopf multiplication makes these evaluations
a group homomorphism, including for the residue field.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WithConv
open scoped TensorProduct

namespace FLT.Mazur.EllipticSubgroupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]
  (R : Type u) [CommRing R] [Algebra A R]

/-- Original integral evaluation with values in a prescribed test algebra. -/
def globalClosureSpecializedEvaluation (P : H) : GlobalClosure A W H →ₐ[A] R :=
  (Algebra.ofId A R).comp (globalClosureEvaluation A W H P)

/-- Specialized evaluation is the original section pulled back along the test algebra. -/
theorem globalClosureSpecializedEvaluation_spec (P : H) :
    Spec.map (CommRingCat.ofHom (globalClosureSpecializedEvaluation A W H R P).toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraMap A R)) ≫ integralSection A W H P ≫
        (gluedClosure A W H 1 2).isoSpec.hom := by
  change Spec.map (CommRingCat.ofHom ((algebraMap A R).comp
    (globalClosureEvaluation A W H P).toRingHom)) = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, globalClosureEvaluation_spec]

omit [Finite H] in
/-- Tensor evaluation commutes with specialization of the value ring. -/
theorem globalClosureSpecializedEvaluation_tensor (P Q : H)
    (t : GlobalClosure A W H ⊗[A] GlobalClosure A W H) :
    Algebra.TensorProduct.productMap (globalClosureSpecializedEvaluation A W H R P)
      (globalClosureSpecializedEvaluation A W H R Q) t =
      algebraMap A R (globalClosureTensorEvaluation A W H P Q t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => exact (map_mul (algebraMap A R) _ _).symm
  | add x y hx hy => simp only [map_add, hx, hy]

variable [IsDedekindDomain A] (hΔ : IsUnit W.Δ)

/-- The test-algebra points of the actual closure carry the recovered convolution group. -/
@[instance_reducible] def globalClosureSpecializedPointGroup :
    letI := globalClosureHopfAlgebra A W H hΔ
    Group (WithConv (GlobalClosure A W H →ₐ[A] R)) := by
  letI := globalClosureHopfAlgebra A W H hΔ
  exact HopfAlgebra.testAlgebraPointGroup A (GlobalClosure A W H) R

/-- Original subgroup addition is convolution after every specialization. -/
def globalClosureSpecialization :
    letI := globalClosureHopfAlgebra A W H hΔ
    Multiplicative H →* WithConv (GlobalClosure A W H →ₐ[A] R) := by
  letI := globalClosureHopfAlgebra A W H hΔ
  refine
    { toFun := fun P => toConv (globalClosureSpecializedEvaluation A W H R P.toAdd)
      map_one' := ?_
      map_mul' := ?_ }
  · apply WithConv.ext
    change (Algebra.ofId A R).comp (globalClosureEvaluation A W H 0) =
      (Algebra.ofId A R).comp (Bialgebra.counitAlgHom A (GlobalClosure A W H))
    rw [globalClosureHopf_counit_eq_evaluation]
  · intro P Q
    apply WithConv.ext
    apply AlgHom.ext
    intro a
    rw [AlgHom.convMul_apply]
    change algebraMap A R (globalClosureEvaluation A W H (P.toAdd + Q.toAdd) a) =
      Algebra.TensorProduct.productMap
        (globalClosureSpecializedEvaluation A W H R P.toAdd)
        (globalClosureSpecializedEvaluation A W H R Q.toAdd) (Coalgebra.comul (R := A) a)
    rw [globalClosureSpecializedEvaluation_tensor]
    exact congrArg (algebraMap A R)
      (AlgHom.congr_fun (globalClosureHopf_comul_evaluation A W H hΔ P.toAdd Q.toAdd) a).symm

/-- Specialization preserves every original torsion relation. -/
theorem globalClosureSpecialization_torsion (P : H) (n : ℕ) (hP : n • P = 0) :
    letI := globalClosureHopfAlgebra A W H hΔ
    globalClosureSpecialization A W H R hΔ (Multiplicative.ofAdd P) ^ n = 1 := by
  let _ := globalClosureHopfAlgebra A W H hΔ
  rw [← map_pow]
  change globalClosureSpecialization A W H R hΔ (Multiplicative.ofAdd (n • P)) = 1
  rw [hP]
  exact map_one _

end FLT.Mazur.EllipticSubgroupChart

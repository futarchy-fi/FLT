/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.SquareZeroConvolutionLift
public import FLT.GroupScheme.PDivisibleSystem
public import Mathlib.Algebra.Module.Projective

/-! # Lifting multiplication of original finite-flat points -/

@[expose] public noncomputable section
open WithConv
namespace HopfAlgebra
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Bialgebra R A] [Coalgebra.IsCocomm R A] [Algebra R B] [Algebra R C]
  [Module.Projective R A]

/-- Projectivity supplies a linear lift; convolution removes its square-zero algebra defect. -/
theorem exists_squareZero_convPow_lift (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (hJ : RingHom.ker q ^ 2 = ⊥) (N : ℕ) (hN : ∀ b ∈ RingHom.ker q, N • b = 0)
    (x : A →ₐ[R] C) : ∃ y : A →ₐ[R] B, q.comp y = (toConv x ^ N).ofConv := by
  obtain ⟨f, hf⟩ := Module.projective_lifting_property q.toLinearMap x.toLinearMap hq
  have hf' (a : A) : q (f a) = x a := LinearMap.congr_fun hf a
  have hone : f 1 - 1 ∈ RingHom.ker q := by
    change q (f 1 - 1) = 0
    rw [map_sub, hf', map_one, map_one, sub_self]
  have hmul (a b : A) : f (a * b) - f a * f b ∈ RingHom.ker q := by
    change q (f (a * b) - f a * f b) = 0
    simp only [map_sub, map_mul, hf', sub_self]
  refine ⟨squareZeroConvolutionLift (RingHom.ker q) hJ N hN f hone hmul, ?_⟩
  apply AlgHom.toLinearMap_injective
  change q.toLinearMap.comp (toConv f ^ N).ofConv = _
  rw [algHom_comp_linear_convPow, hf, ← AlgHom.toLinearMap_convPow]

end HopfAlgebra
namespace ThreeAdicPlan
variable {R K B C : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C]

omit [IsLocalRing R] in
/-- The original multiplication morphism acts by convolution on every algebra-valued point. -/
theorem FF.point_comp_multiply (X : FF R K) (N : ℕ) (x : X.CoordinateRing →ₐ[R] C) :
    x.comp (X.multiply N).toAlgHom = (toConv x ^ N).ofConv := by
  have he := congrArg WithConv.ofConv
    (BialgHom.toAlgHom_convPow (toConv (BialgHom.id R X.CoordinateRing)) N)
  change (X.multiply N).toAlgHom = (toConv (AlgHom.id R X.CoordinateRing) ^ N).ofConv at he
  rw [he, HopfAlgebra.comp_convPow, AlgHom.comp_id]

/-- Across a square-zero thickening annihilated by N, [N]x lifts on the original model. -/
theorem FF.exists_multiply_lift (X : FF R K) (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (hJ : RingHom.ker q ^ 2 = ⊥) (N : ℕ) (hN : ∀ b ∈ RingHom.ker q, N • b = 0)
    (x : X.CoordinateRing →ₐ[R] C) :
    ∃ y : X.CoordinateRing →ₐ[R] B, q.comp y = x.comp (X.multiply N).toAlgHom := by
  rw [X.point_comp_multiply]
  let : Module.Free R X.CoordinateRing := Module.free_of_flat_of_isLocalRing
  exact HopfAlgebra.exists_squareZero_convPow_lift q hq hJ N hN x

end ThreeAdicPlan

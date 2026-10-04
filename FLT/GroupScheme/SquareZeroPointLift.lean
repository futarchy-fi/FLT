/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatSquareZeroLifting

/-! # Canonical lifting of multiplication across a square-zero thickening -/

@[expose] public noncomputable section
open WithConv
namespace HopfAlgebra
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Bialgebra R A] [Coalgebra.IsCocomm R A] [Algebra R B] [Algebra R C]
  [Module.Projective R A]
  (q : B →ₐ[R] C) (hq : Function.Surjective q) (hJ : RingHom.ker q ^ 2 = ⊥)
  (N : ℕ) (hN : ∀ b ∈ RingHom.ker q, N • b = 0) (x : A →ₐ[R] C)
include hq hJ hN

/-- The N-th convolution power is independent of every choice of linear lift. -/
theorem exists_convPow_of_every_linear_lift :
    ∃ y : A →ₐ[R] B, ∀ f : A →ₗ[R] B, q.toLinearMap.comp f = x.toLinearMap →
      y.toLinearMap = (toConv f ^ N).ofConv := by
  obtain ⟨f, hf⟩ := Module.projective_lifting_property q.toLinearMap x.toLinearMap hq
  have hf' (a : A) : q (f a) = x a := LinearMap.congr_fun hf a
  have hone : f 1 - 1 ∈ RingHom.ker q := by
    change q (f 1 - 1) = 0
    simp only [map_sub, hf', map_one, sub_self]
  have hmul (a b : A) : f (a * b) - f a * f b ∈ RingHom.ker q := by
    change q (f (a * b) - f a * f b) = 0
    simp only [map_sub, map_mul, hf', sub_self]
  refine ⟨squareZeroConvolutionLift (RingHom.ker q) hJ N hN f hone hmul, ?_⟩
  intro g hg
  apply congrArg WithConv.ofConv
  apply convPow_eq_of_sub_mem (RingHom.ker q) hJ N hN f g
  intro a
  change q (f a - g a) = 0
  rw [map_sub, hf', show q (g a) = x a from LinearMap.congr_fun hg a, sub_self]

/-- Canonical lift of multiplication; the preceding theorem proves independence of choices. -/
def squareZeroPointLift : A →ₐ[R] B :=
  (exists_convPow_of_every_linear_lift q hq hJ N hN x).choose

/-- Any linear lift computes the same canonical point. -/
theorem squareZeroPointLift_eq_convPow (f : A →ₗ[R] B)
    (hf : q.toLinearMap.comp f = x.toLinearMap) :
    (squareZeroPointLift q hq hJ N hN x).toLinearMap = (toConv f ^ N).ofConv :=
  (exists_convPow_of_every_linear_lift q hq hJ N hN x).choose_spec f hf

/-- The quotient of the canonical point is the prescribed multiple of the original point. -/
theorem squareZeroPointLift_reduction :
    q.comp (squareZeroPointLift q hq hJ N hN x) = (toConv x ^ N).ofConv := by
  obtain ⟨f, hf⟩ := Module.projective_lifting_property q.toLinearMap x.toLinearMap hq
  apply AlgHom.toLinearMap_injective
  rw [AlgHom.comp_toLinearMap, squareZeroPointLift_eq_convPow q hq hJ N hN x f hf,
    algHom_comp_linear_convPow, hf, ← AlgHom.toLinearMap_convPow]

/-- If the point already lifts as an algebra map, its N-th power is the canonical lift. -/
theorem squareZeroPointLift_eq_of_algHom (z : A →ₐ[R] B) (hz : q.comp z = x) :
    squareZeroPointLift q hq hJ N hN x = (toConv z ^ N).ofConv := by
  apply AlgHom.toLinearMap_injective
  rw [squareZeroPointLift_eq_convPow q hq hJ N hN x z.toLinearMap
    (congrArg AlgHom.toLinearMap hz), ← AlgHom.toLinearMap_convPow]

end HopfAlgebra

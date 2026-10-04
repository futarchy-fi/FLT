/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.SquareZeroPointLift

/-! # The canonical square-zero multiplication lift preserves the group law -/

@[expose] public noncomputable section
open WithConv
namespace HopfAlgebra
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Bialgebra R A] [Coalgebra.IsCocomm R A] [Algebra R B] [Algebra R C]
  [Module.Projective R A]
  (q : B →ₐ[R] C) (hq : Function.Surjective q) (hJ : RingHom.ker q ^ 2 = ⊥)
  (N : ℕ) (hN : ∀ b ∈ RingHom.ker q, N • b = 0)

omit [Coalgebra.IsCocomm R A] [Module.Projective R A] in
/-- Convolution of any two linear lifts lifts the product of their original points. -/
theorem linearLift_convMul (x y : A →ₐ[R] C) (f g : A →ₗ[R] B)
    (hf : q.toLinearMap.comp f = x.toLinearMap)
    (hg : q.toLinearMap.comp g = y.toLinearMap) :
    q.toLinearMap.comp (toConv f * toConv g).ofConv = (toConv x * toConv y).ofConv.toLinearMap := by
  rw [LinearMap.algHom_comp_convMul_distrib, hf, hg]
  exact congrArg ofConv (AlgHom.toLinearMap_convMul (toConv x) (toConv y)).symm

/-- The canonical lift is multiplicative for the original convolution group law. -/
theorem squareZeroPointLift_convMul (x y : A →ₐ[R] C) :
    squareZeroPointLift q hq hJ N hN (toConv x * toConv y).ofConv =
      (toConv (squareZeroPointLift q hq hJ N hN x) *
        toConv (squareZeroPointLift q hq hJ N hN y)).ofConv := by
  obtain ⟨f, hf⟩ := Module.projective_lifting_property q.toLinearMap x.toLinearMap hq
  obtain ⟨g, hg⟩ := Module.projective_lifting_property q.toLinearMap y.toLinearMap hq
  apply AlgHom.toLinearMap_injective
  apply (WithConv.linearEquiv R (A →ₗ[R] B)).symm.injective
  change toConv _ = toConv _
  rw [squareZeroPointLift_eq_convPow q hq hJ N hN _ _ (linearLift_convMul q x y f g hf hg),
    AlgHom.toLinearMap_convMul, squareZeroPointLift_eq_convPow q hq hJ N hN x f hf,
    squareZeroPointLift_eq_convPow q hq hJ N hN y g hg]
  exact mul_pow (toConv f) (toConv g) N

/-- The canonical lift preserves the original augmentation. -/
theorem squareZeroPointLift_one :
    squareZeroPointLift q hq hJ N hN (1 : WithConv (A →ₐ[R] C)).ofConv =
      (1 : WithConv (A →ₐ[R] B)).ofConv := by
  have he : q.comp (1 : WithConv (A →ₐ[R] B)).ofConv =
      (1 : WithConv (A →ₐ[R] C)).ofConv := by
    ext a
    exact q.commutes _
  rw [squareZeroPointLift_eq_of_algHom q hq hJ N hN _ _ he, toConv_ofConv, one_pow]

/-- Packaging the proved laws makes every natural multiple available without new choices. -/
def squareZeroPointLiftMonoidHom : WithConv (A →ₐ[R] C) →* WithConv (A →ₐ[R] B) where
  toFun x := toConv (squareZeroPointLift q hq hJ N hN x.ofConv)
  map_one' := congrArg toConv (squareZeroPointLift_one q hq hJ N hN)
  map_mul' x y := congrArg toConv (squareZeroPointLift_convMul q hq hJ N hN x.ofConv y.ofConv)

end HopfAlgebra

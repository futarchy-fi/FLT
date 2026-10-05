/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleFormalCotangent
public import FLT.GroupScheme.PDivisiblePointColimitGroup
public import FLT.GroupScheme.InfinitesimalCotangentAddition

/-! # The original reduction kernel as the additive cotangent dual -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  (X : PDivisibleSystem R K p height)

open WithConv

/-- Use the original finite-level convolution when evaluating the colimit homomorphism. -/
local instance kernelLevelPointGroup (n : ℕ) :
    CommGroup ((X.level n).CoordinateRing →ₐ[R] B) := by
  letI : CommGroup (WithConv ((X.level n).CoordinateRing →ₐ[R] B)) :=
    { HopfAlgebra.testAlgebraPointGroup R (X.level n).CoordinateRing B with
      mul_comm := mul_comm }
  exact (WithConv.equiv _).symm.commGroup

/-- The colimit augmentation is the identity for the original convolution law. -/
theorem pointColimitMk_augmentation_eq_one (n : ℕ) :
    X.pointColimitMk n (X.levelAugmentation (B := B) n) = 1 :=
  (X.pointColimitMkHom n).map_one'

/-- The previously defined infinitesimal points are the actual group-theoretic kernel. -/
def pointKernelInfinitesimalEquiv (q : B →ₐ[R] C) :
    (X.pointColimitMapHom q).ker ≃ X.InfinitesimalColimit q where
  toFun z := ⟨z.val, z.property.trans (X.pointColimitMk_augmentation_eq_one 0).symm⟩
  invFun z := ⟨z.val, z.property.trans (X.pointColimitMk_augmentation_eq_one 0)⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [∀ n, Finite (X.LevelCotangent n)]
  (q : B →ₐ[R] C) (hJ : RingHom.ker q ^ 2 = ⊥)
  (r : ℕ) (hr : ∀ b : RingHom.ker q, p ^ r • b = 0)

/-- Cotangent coordinates on the actual square-zero reduction kernel. -/
def pointKernelCotangentEquiv :
    (X.pointColimitMapHom q).ker ≃ (X.cotangentLimit →ₗ[R] RingHom.ker q) :=
  (X.pointKernelInfinitesimalEquiv q).trans (X.formalInfinitesimalCotangentEquiv q hJ r hr)

/-- Kernel coordinates agree with the original finite-level cotangent evaluation. -/
theorem pointKernelCotangentEquiv_mk (n : ℕ) (f : X.LevelInfinitesimalKernel q n) :
    X.pointKernelCotangentEquiv q hJ r hr
      ⟨X.pointColimitMk n f.val, by
        change X.pointColimitMap q (X.pointColimitMk n f.val) = 1
        rw [X.pointColimitMap_mk, f.property]
        exact X.pointColimitMk_augmentation_eq_one n⟩ =
      X.infinitesimalLimitPairing q hJ n f :=
  X.formalInfinitesimalCotangentEquiv_mk q hJ r hr n f

/-- Original convolution becomes addition, not merely a bijection of underlying sets. -/
theorem pointKernelCotangentEquiv_mul (x y : (X.pointColimitMapHom q).ker) :
    X.pointKernelCotangentEquiv q hJ r hr (x * y) =
      X.pointKernelCotangentEquiv q hJ r hr x +
        X.pointKernelCotangentEquiv q hJ r hr y := by
  obtain ⟨f, hf⟩ := X.infinitesimalColimitMk_surjective q hJ r hr
    (X.pointKernelInfinitesimalEquiv q x)
  obtain ⟨g, hg⟩ := X.infinitesimalColimitMk_surjective q hJ r hr
    (X.pointKernelInfinitesimalEquiv q y)
  let z := HopfAlgebra.augmentationKernelConv q f g
  have hx : x.val = X.pointColimitMk r f.val := (congrArg Subtype.val hf).symm
  have hy : y.val = X.pointColimitMk r g.val := (congrArg Subtype.val hg).symm
  have hz : X.pointKernelInfinitesimalEquiv q (x * y) =
      X.infinitesimalColimitMk q r z := by
    apply Subtype.ext
    change x.val * y.val = X.pointColimitMk r z.val
    rw [hx, hy]
    exact ((X.pointColimitMkHom r).map_mul' f.val g.val).symm
  change X.formalInfinitesimalCotangentEquiv q hJ r hr
    (X.pointKernelInfinitesimalEquiv q (x * y)) = _
  rw [hz, X.formalInfinitesimalCotangentEquiv_mk]
  change X.infinitesimalLimitPairing q hJ r z =
    X.formalInfinitesimalCotangentEquiv q hJ r hr (X.pointKernelInfinitesimalEquiv q x) +
      X.formalInfinitesimalCotangentEquiv q hJ r hr (X.pointKernelInfinitesimalEquiv q y)
  rw [← hf, ← hg, X.formalInfinitesimalCotangentEquiv_mk,
    X.formalInfinitesimalCotangentEquiv_mk]
  unfold infinitesimalLimitPairing
  rw [HopfAlgebra.augmentationPointCotangentEquiv_conv]
  rfl

/-- A group equivalence with the additive original cotangent dual. -/
def pointKernelCotangentMulEquiv :
    (X.pointColimitMapHom q).ker ≃* Multiplicative (X.cotangentLimit →ₗ[R] RingHom.ker q) where
  toEquiv := (X.pointKernelCotangentEquiv q hJ r hr).trans Multiplicative.ofAdd
  map_mul' := X.pointKernelCotangentEquiv_mul q hJ r hr

end ThreeAdicPlan.PDivisibleSystem

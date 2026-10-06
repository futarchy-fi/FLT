/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionHopfPoints
public import FLT.GroupScheme.HopfDifferentials
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Units

/-! # Differentials of the actual nonzero-order torsion group -/

@[expose] public noncomputable section
open scoped TensorProduct
open WithConv
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R]

/-- Commutativity of the two universal tensor-valued points detects cocommutativity. -/
theorem coalgebra_isCocomm_of_tensor_points (A : Type u) [CommRing A] [Bialgebra R A]
    (h : ∀ f g : WithConv (A →ₐ[R] A ⊗[R] A), f * g = g * f) :
    Coalgebra.IsCocomm R A := by
  have hl : Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A)
      Algebra.TensorProduct.includeRight (fun _ _ => Commute.all ..) =
      AlgHom.id R (A ⊗[R] A) := by
    ext <;> simp
  have hr : Algebra.TensorProduct.lift (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A)
      Algebra.TensorProduct.includeLeft (fun _ _ => Commute.all ..) =
      (Algebra.TensorProduct.comm R A A).toAlgHom := by
    ext <;> simp
  constructor
  apply LinearMap.ext
  intro a
  have ha := congrArg (fun f : WithConv (A →ₐ[R] A ⊗[R] A) => f a)
    (h (toConv Algebra.TensorProduct.includeLeft) (toConv Algebra.TensorProduct.includeRight))
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply, hl, hr] at ha
  exact ha.symm

variable (W : WeierstrassCurve R)
variable [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]

instance torsionCoordinateIsCocomm (n : ℕ) [NeZero n] :
    Coalgebra.IsCocomm R (torsionCoordinateRing W n) :=
  coalgebra_isCocomm_of_tensor_points _ (torsionCoordinatePoint_mul_comm W n _)

/-- The torsion order annihilates all differentials of the actual coordinate algebra. -/
theorem torsionCoordinateDifferential_nsmul (n : ℕ) [NeZero n]
    (ω : KaehlerDifferential R (torsionCoordinateRing W n)) : n • ω = 0 :=
  HopfAlgebra.nsmul_kaehlerDifferential_eq_zero n
    (torsionCoordinatePoint_pow_eq_one W n _ (toConv (AlgHom.id R _))) ω

/-- Invertible-order torsion has a formally unramified coordinate algebra. -/
theorem torsionCoordinate_formallyUnramified (n : ℕ) [NeZero n]
    (hn : IsUnit (n : R)) : Algebra.FormallyUnramified R (torsionCoordinateRing W n) := by
  constructor
  apply subsingleton_of_forall_eq 0
  intro ω
  apply hn.smul_eq_zero.mp
  simpa only [Nat.cast_smul_eq_nsmul] using torsionCoordinateDifferential_nsmul W n ω

end WeierstrassCurve.CubicCharts

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.IntegralModelPoints
public import FLT.GroupScheme.FiniteFlatScalarExtension
public import FLT.GroupScheme.DiagonalizableFiniteFlat

/-!
# Diagonalizable models over a general integral base

The coordinate algebra is the integral group algebra. Its geometric points
are the actual characters of the degree group, with convolution and field action.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace ThreeAdicPlan

variable (R K A : Type) [CommRing R] [Field K] [Algebra R K] [CharZero K]
  [AddCommGroup A] [Finite A]

/-- The split diagonalizable model on a finite character group. -/
@[implicit_reducible]
def diagonalGroupModel : FF R K := by
  let : NeZero (Nat.card (Multiplicative A) : K) :=
    ⟨by exact_mod_cast Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩⟩
  let : Algebra.Etale K (MonoidAlgebra K (Multiplicative A)) :=
    Algebra.etale_of_finite_reduced K (MonoidAlgebra K (Multiplicative A))
  let : Algebra.Etale K (K ⊗[R] MonoidAlgebra R (Multiplicative A)) :=
    Algebra.Etale.of_equiv (MonoidAlgebra.scalarTensorEquiv R K).symm
  let : HopfAlgebra.IsFiniteFlat R (MonoidAlgebra R (Multiplicative A)) := ⟨⟩
  exact FF.ofCoordinateRing (MonoidAlgebra R (Multiplicative A))

/-- A character evaluates the integral group-algebra generators. -/
def diagonalGroupPoint (χ : Multiplicative A →* AlgebraicClosure K) :
    (diagonalGroupModel R K A).Points :=
  (diagonalGroupModel R K A).integralPoints.symm (MonoidAlgebra.lift R _ _ χ)

/-- Every geometric point is obtained from exactly one character. -/
def diagonalGroupPointEquiv :
    (Multiplicative A →* AlgebraicClosure K) ≃ (diagonalGroupModel R K A).Points :=
  (MonoidAlgebra.lift R _ _).trans (diagonalGroupModel R K A).integralPoints.symm

/-- Integral evaluation of a constructed point reads its character. -/
@[simp] theorem diagonalGroupPoint_single (χ : Multiplicative A →* AlgebraicClosure K)
    (a : Multiplicative A) :
    (diagonalGroupModel R K A).integralPoints (diagonalGroupPoint R K A χ)
      (MonoidAlgebra.single a 1) = χ a := by
  unfold diagonalGroupPoint
  rw [Equiv.apply_symm_apply]
  change (MonoidAlgebra.lift R _ _ χ) (MonoidAlgebra.single a 1) = χ a
  simp only [MonoidAlgebra.lift_single, one_smul]

/-- Geometric points are determined by the group-like integral generators. -/
theorem diagonalGroupPoint_ext {x y : (diagonalGroupModel R K A).Points}
    (h : ∀ a, (diagonalGroupModel R K A).integralPoints x (MonoidAlgebra.single a 1) =
      (diagonalGroupModel R K A).integralPoints y (MonoidAlgebra.single a 1)) : x = y := by
  apply (diagonalGroupModel R K A).integralPoints.injective
  exact MonoidAlgebra.algHom_ext h (Subsingleton.elim _ _)

/-- Character multiplication is the actual geometric addition. -/
theorem diagonalGroupPoint_mul (χ ψ : Multiplicative A →* AlgebraicClosure K) :
    diagonalGroupPoint R K A (χ * ψ) =
      diagonalGroupPoint R K A χ + diagonalGroupPoint R K A ψ := by
  apply diagonalGroupPoint_ext
  intro a
  rw [FF.integralPoints_add]
  simp only [AlgHom.comp_apply]
  change _ = Algebra.TensorProduct.lift _ _ _ (Coalgebra.comul (R := R)
    (MonoidAlgebra.single a 1))
  rw [(MonoidAlgebra.isGroupLikeElem_single_one a).comul_eq_tmul_self,
    Algebra.TensorProduct.lift_tmul]
  exact (diagonalGroupPoint_single R K A (χ * ψ) a).trans
    (congrArg₂ (· * ·) (diagonalGroupPoint_single R K A χ a).symm
      (diagonalGroupPoint_single R K A ψ a).symm)

/-- Field automorphisms act on the values of the character. -/
theorem diagonalGroupPoint_smul (χ : Multiplicative A →* AlgebraicClosure K)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    g • diagonalGroupPoint R K A χ =
      diagonalGroupPoint R K A (g.toMonoidHom.comp χ) := by
  apply diagonalGroupPoint_ext
  intro a
  rw [FF.integralPoints_smul]
  simp

end ThreeAdicPlan

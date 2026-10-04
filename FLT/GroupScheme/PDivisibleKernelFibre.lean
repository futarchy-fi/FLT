/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfPointedFibre
public import FLT.GroupScheme.PDivisibleSystem

/-! # Pointed division fibres with the original finite kernel level -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height) (m n : ℕ)

/-- The augmentation quotient is the original kernel level, via its original inclusion. -/
def reductionKernelEquiv :
    ((X.level (m + n)).CoordinateRing ⧸
      HopfAlgebra.augmentationIdeal (X.reduction (Nat.le_add_left n m))) ≃ₐ[R]
        (X.level m).CoordinateRing :=
  (Ideal.quotientEquivAlgOfEq R (X.kernel m n)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (X.closed (Nat.le_add_right m n)))

/-- The kernel identification retains the actual closed-inclusion coordinate map. -/
@[simp]
theorem reductionKernelEquiv_mk (a : (X.level (m + n)).CoordinateRing) :
    X.reductionKernelEquiv m n (Ideal.Quotient.mk _ a) =
      X.inclusion (Nat.le_add_right m n) a := rfl

variable {S : Type} [CommRing S] [Algebra R S]
  [Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing]
  [IsScalarTower R (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing]
  [Algebra (X.level n).CoordinateRing S]
  [Algebra (X.level (m + n)).CoordinateRing S]
  [IsScalarTower R (X.level (m + n)).CoordinateRing S]
  [IsScalarTower (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing S]

/-- A pointed original division fibre is the base change of the original kernel group. -/
def pointedDivisionFibreEquiv
    (hf : (X.reduction (Nat.le_add_left n m)).toAlgHom =
      IsScalarTower.toAlgHom R (X.level n).CoordinateRing
        (X.level (m + n)).CoordinateRing) :
    S ⊗[(X.level n).CoordinateRing] (X.level (m + n)).CoordinateRing ≃ₐ[S]
      S ⊗[R] (X.level m).CoordinateRing :=
  (HopfAlgebra.pointedFibreEquiv (S := S) _ hf).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
      (X.reductionKernelEquiv m n))

/-- The fibre coordinate map uses the comultiplication and the original kernel inclusion. -/
theorem pointedDivisionFibreEquiv_one_tmul
    (hf : (X.reduction (Nat.le_add_left n m)).toAlgHom =
      IsScalarTower.toAlgHom R (X.level n).CoordinateRing
        (X.level (m + n)).CoordinateRing) (a : (X.level (m + n)).CoordinateRing) :
    X.pointedDivisionFibreEquiv m n hf (1 ⊗ₜ[(X.level n).CoordinateRing] a) =
      Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R (X.level (m + n)).CoordinateRing S)
        (X.inclusion (Nat.le_add_right m n)).toAlgHom (Coalgebra.comul a) := by
  simp only [pointedDivisionFibreEquiv, AlgEquiv.trans_apply,
    HopfAlgebra.pointedFibreEquiv_one_tmul, Algebra.TensorProduct.congr_apply,
    HopfAlgebra.torsorCoaction, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
  generalize Coalgebra.comul (R := R) a = z
  induction z using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end ThreeAdicPlan.PDivisibleSystem

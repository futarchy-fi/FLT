/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualBaseChange
public import FLT.GroupScheme.HopfPoints
public import FLT.GroupScheme.EtaleOrder
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Jacobson.Semiprimary

/-!
# The étale generic fibre of an integral Cartier dual

Over a separably closed field, the dual of a finite étale Hopf algebra is
the group algebra of its points. In characteristic zero Maschke's theorem
makes this algebra reduced and hence étale. Faithfully flat descent gives
the result over an arbitrary characteristic-zero field.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace HopfAlgebra.CartierDual

variable (K A : Type) [Field K] [CommRing A] [HopfAlgebra K A]
  [Coalgebra.IsCocomm K A]

attribute [local instance] HopfAlgebra.pointsCommGroup

/-- Algebra-valued points embed multiplicatively in the convolution dual. -/
def pointMonoidHom : (A →ₐ[K] K) →* CartierDual K A where
  toFun φ := WithConv.toConv φ.toLinearMap
  map_one' := rfl
  map_mul' φ ψ := by
    apply WithConv.ext
    ext a
    change Algebra.TensorProduct.lift φ ψ (fun _ _ ↦ Commute.all _ _)
      (Coalgebra.comul a) =
        LinearMap.mul' K K (TensorProduct.map φ.toLinearMap ψ.toLinearMap (Coalgebra.comul a))
    induction Coalgebra.comul (R := K) a using TensorProduct.inductionOn with
    | tmul a b => rfl
    | add x y hx hy => simp [hx, hy]

/-- Linear extension of points gives the group-algebra map to the dual. -/
def pointBasisAlgHom : MonoidAlgebra K (A →ₐ[K] K) →ₐ[K] CartierDual K A :=
  MonoidAlgebra.lift K _ _ (pointMonoidHom K A)

omit [Coalgebra.IsCocomm K A] in
/-- Each group-like basis vector maps to its evaluation functional. -/
@[simp] theorem pointBasisAlgHom_single (φ : A →ₐ[K] K) (a : A) :
    pointBasisAlgHom K A (MonoidAlgebra.single φ 1) a = φ a := by
  simp only [pointBasisAlgHom, MonoidAlgebra.lift_single, one_smul]
  rfl

omit [Coalgebra.IsCocomm K A] in
/-- Distinct algebra maps are linearly independent, so the group-algebra
map into the convolution dual is injective. -/
theorem pointBasisAlgHom_injective : Function.Injective (pointBasisAlgHom K A) := by
  have he : (pointBasisAlgHom K A).toLinearMap =
      (MonoidAlgebra.basis (A →ₐ[K] K) K).constr K
        (fun φ ↦ WithConv.toConv φ.toLinearMap) := by
    apply (MonoidAlgebra.basis (A →ₐ[K] K) K).ext
    intro φ
    rw [Module.Basis.constr_basis]
    change pointBasisAlgHom K A (MonoidAlgebra.single φ 1) = WithConv.toConv φ.toLinearMap
    simp only [pointBasisAlgHom, MonoidAlgebra.lift_single, one_smul]
    rfl
  change Function.Injective (pointBasisAlgHom K A).toLinearMap
  rw [he]
  apply Module.Basis.injective_constr_of_linearIndependent
  exact (linearIndependent_algHom_toLinearMap K A K).map'
    (linearEquiv (R := K) (A := A)).symm.toLinearMap
    (LinearMap.ker_eq_bot.mpr (linearEquiv (R := K) (A := A)).symm.injective)

variable [Module.Finite K A] [Algebra.Etale K A] [IsSepClosed K]

/-- Over a separably closed field the dual of a finite étale Hopf algebra
is the group algebra of its full point group. -/
def pointBasisAlgEquiv : MonoidAlgebra K (A →ₐ[K] K) ≃ₐ[K] CartierDual K A := by
  let := Fintype.ofFinite (A →ₐ[K] K)
  have hd : Module.finrank K (MonoidAlgebra K (A →ₐ[K] K)) =
      Module.finrank K (CartierDual K A) := by
    rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis (A →ₐ[K] K) K),
      Fintype.card_eq_nat_card, (linearEquiv (R := K) (A := A)).finrank_eq,
      Subspace.dual_finrank_eq, GaloisModule.finrank_eq_natCard_algHom K K A]
  exact AlgEquiv.ofBijective (pointBasisAlgHom K A)
    ⟨pointBasisAlgHom_injective K A,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd
        (f := (pointBasisAlgHom K A).toLinearMap)).mp
        (pointBasisAlgHom_injective K A)⟩

/-- Maschke's theorem makes the dual algebra étale in characteristic zero. -/
theorem etale_of_isSepClosed [CharZero K] : Algebra.Etale K (CartierDual K A) := by
  let : NeZero (Nat.card (A →ₐ[K] K) : K) :=
    ⟨by exact_mod_cast Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩⟩
  let : Algebra.Etale K (MonoidAlgebra K (A →ₐ[K] K)) :=
    Algebra.etale_of_finite_reduced K _
  exact Algebra.Etale.of_equiv (pointBasisAlgEquiv K A)

omit [IsSepClosed K] in
/-- The dual of a finite étale commutative, cocommutative Hopf algebra over
any characteristic-zero field is again étale. -/
theorem etale [CharZero K] : Algebra.Etale K (CartierDual K A) := by
  let : Algebra.Etale (AlgebraicClosure K)
      (CartierDual (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A)) :=
    etale_of_isSepClosed (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A)
  let : Algebra.Etale (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] CartierDual K A) :=
    Algebra.Etale.of_equiv (baseChangeAlgEquiv (AlgebraicClosure K)).symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat (AlgebraicClosure K)

end HopfAlgebra.CartierDual

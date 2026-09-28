/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualGeometric

/-!
# The geometric Cartier pairing and its Galois action

A geometric point of the original algebra determines an element of the
scalar-extended dual. In a finite basis this is the usual evaluation tensor,
so the character comparison respects Galois conjugation on both arguments.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace HopfAlgebra.CartierDual

variable (K L A : Type) [Field K] [Field L] [Algebra K L] [CommRing A]
  [HopfAlgebra K A] [Coalgebra.IsCocomm K A]
  [Module.Finite K A] [Algebra.Etale K A] [IsSepClosed L]

attribute [local instance] HopfAlgebra.pointsCommGroup

/-- The element of the scalar-extended integral dual representing a geometric point. -/
def geometricPointElement (p : A →ₐ[K] L) : L ⊗[K] CartierDual K A :=
  geometricGroupAlgebraEquiv K L A (MonoidAlgebra.single p 1)

omit [Coalgebra.IsCocomm K A] in
/-- The element representing a geometric point evaluates as that point. -/
@[simp] theorem geometricPointElement_eval (p : A →ₐ[K] L) (a : A) :
    baseChangeAlgEquiv L (geometricPointElement K L A p) (1 ⊗ₜ a) = p a := by
  simp only [geometricPointElement, geometricGroupAlgebraEquiv, AlgEquiv.trans_apply,
    MonoidAlgebra.domCongr_single, AlgEquiv.apply_symm_apply]
  change pointBasisAlgHom L (L ⊗[K] A)
    (MonoidAlgebra.single (scalarPointsEquiv K L A p) 1) (1 ⊗ₜ a) = _
  rw [pointBasisAlgHom_single, scalarPointsEquiv_tmul, one_mul]

omit [Coalgebra.IsCocomm K A] in
/-- The geometric evaluation tensor can be computed in any finite basis. -/
theorem geometricPointElement_eq_sum {ι : Type} [Fintype ι]
    (b : Module.Basis ι K A) (p : A →ₐ[K] L) :
    geometricPointElement K L A p =
      ∑ i, p (b i) ⊗ₜ[K] WithConv.toConv (b.coord i) := by
  apply (baseChangeAlgEquiv (R := K) (A := A) L).injective
  apply WithConv.ext
  apply (TensorProduct.isBaseChange K A L).algHom_ext
  intro a
  change baseChangeAlgEquiv L (geometricPointElement K L A p) (1 ⊗ₜ a) =
    baseChangeAlgEquiv L (∑ i, p (b i) ⊗ₜ[K] WithConv.toConv (b.coord i)) (1 ⊗ₜ a)
  rw [geometricPointElement_eval]
  simp only [map_sum]
  conv_lhs => rw [← b.sum_repr a]
  simp [Algebra.smul_def, mul_comm]

/-- The geometric character comparison is evaluation on the point tensor. -/
theorem geometricCharactersEquiv_apply (ψ : CartierDual K A →ₐ[K] L) (p : A →ₐ[K] L) :
    (geometricCharactersEquiv K L A ψ p : L) =
      AlgHom.liftEquiv K L (CartierDual K A) L ψ (geometricPointElement K L A p) := rfl

/-- In a finite basis, the Cartier pairing is the sum of paired coordinates. -/
theorem geometricCharactersEquiv_eq_sum {ι : Type} [Fintype ι]
    (b : Module.Basis ι K A) (ψ : CartierDual K A →ₐ[K] L) (p : A →ₐ[K] L) :
    (geometricCharactersEquiv K L A ψ p : L) =
      ∑ i, p (b i) * ψ (WithConv.toConv (b.coord i)) := by
  rw [geometricCharactersEquiv_apply, geometricPointElement_eq_sum K L A b]
  simp

/-- The geometric character comparison respects the contragredient Galois action. -/
theorem geometricCharactersEquiv_smul (σ : L ≃ₐ[K] L)
    (ψ : CartierDual K A →ₐ[K] L) (p : A →ₐ[K] L) :
    geometricCharactersEquiv K L A (σ • ψ) p =
      σ • geometricCharactersEquiv K L A ψ (σ⁻¹ • p) := by
  let b := Module.Free.chooseBasis K A
  apply Units.ext
  rw [geometricCharactersEquiv_eq_sum K L A b]
  change _ = σ (geometricCharactersEquiv K L A ψ (σ⁻¹ • p) : L)
  rw [geometricCharactersEquiv_eq_sum K L A b]
  change (∑ i, p (b i) * σ (ψ (WithConv.toConv (b.coord i)))) =
    σ (∑ i, σ.symm (p (b i)) * ψ (WithConv.toConv (b.coord i)))
  simp

end HopfAlgebra.CartierDual

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualEtale

/-!
# Geometric characters of an integral Cartier dual

After extending scalars to a separably closed field, the convolution dual
is the group algebra of the original geometric points. Its points are
therefore precisely the multiplicative characters of that full point group.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Coalgebra

namespace HopfAlgebra.CartierDual

variable (K L A : Type) [Field K] [Field L] [Algebra K L] [CommRing A]
  [HopfAlgebra K A] [Coalgebra.IsCocomm K A]

attribute [local instance] HopfAlgebra.pointsCommGroup

/-- Scalar extension preserves the full convolution group of geometric points. -/
def scalarPointsEquiv : (A →ₐ[K] L) ≃* (L ⊗[K] A →ₐ[L] L) :=
  MulEquiv.symm
  { (AlgHom.liftEquiv K L A L).symm with
    map_mul' := by
      intro φ ψ
      ext a
      change Algebra.TensorProduct.lift φ ψ (fun _ _ ↦ Commute.all _ _)
        (Coalgebra.comul (R := L) (1 ⊗ₜ[K] a)) =
          Algebra.TensorProduct.lift ((AlgHom.liftEquiv K L A L).symm φ)
            ((AlgHom.liftEquiv K L A L).symm ψ) (fun _ _ ↦ Commute.all _ _)
              (Coalgebra.comul (R := K) a)
      rw [TensorProduct.comul_tmul, ← (ℛ K a).eq]
      simp [TensorProduct.tmul_sum] }

omit [Coalgebra.IsCocomm K A] in
/-- Scalar extension evaluates a pure tensor by multiplying its scalar and point value. -/
@[simp] theorem scalarPointsEquiv_tmul (φ : A →ₐ[K] L) (s : L) (a : A) :
    scalarPointsEquiv K L A φ (s ⊗ₜ a) = s * φ a := rfl

variable [Module.Finite K A] [Algebra.Etale K A] [IsSepClosed L]

/-- The generic dual algebra is the group algebra of the complete geometric
point group of the original algebra. -/
def geometricGroupAlgebraEquiv :
    MonoidAlgebra L (A →ₐ[K] L) ≃ₐ[L] L ⊗[K] CartierDual K A :=
  (MonoidAlgebra.domCongr L L (scalarPointsEquiv K L A)).trans
    ((pointBasisAlgEquiv L (L ⊗[K] A)).trans (baseChangeAlgEquiv L).symm)

/-- Geometric points of the dual correspond to unit-valued multiplicative
characters of the complete original geometric point group. -/
def geometricCharactersEquiv : (CartierDual K A →ₐ[K] L) ≃ ((A →ₐ[K] L) →* Lˣ) :=
  (AlgHom.liftEquiv K L (CartierDual K A) L).trans
    ((AlgEquiv.arrowCongr (geometricGroupAlgebraEquiv K L A).symm
      (AlgEquiv.refl : L ≃ₐ[L] L)).trans
        ((MonoidAlgebra.lift L L (A →ₐ[K] L)).symm.trans
          MonoidHom.toHomUnitsMulEquiv.toEquiv))

end HopfAlgebra.CartierDual

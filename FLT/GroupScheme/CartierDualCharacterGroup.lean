/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualBaseChangeHopf
public import FLT.GroupScheme.CartierDualPairing

/-!
# Cartier duality on geometric point groups

The tensor representing a geometric point is group-like. Consequently the
geometric character comparison preserves convolution multiplication, in
addition to its Galois equivariance.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace HopfAlgebra.CartierDual

variable (K L A : Type) [Field K] [Field L] [Algebra K L] [CommRing A]
  [HopfAlgebra K A] [Coalgebra.IsCocomm K A]
  [Module.Finite K A] [Algebra.Etale K A] [IsSepClosed L]

attribute [local instance] HopfAlgebra.pointsCommGroup

omit [Coalgebra.IsCocomm K A] in
/-- The tensor representing a point is group-like for the integral dual comultiplication. -/
theorem geometricPointElement_comul (p : A →ₐ[K] L) :
    Coalgebra.comul (R := L) (geometricPointElement K L A p) =
      geometricPointElement K L A p ⊗ₜ[L] geometricPointElement K L A p := by
  apply baseChange_tensor_ext L
  intro a b
  rw [baseChange_comul_eval, baseChangeTensorEquiv_tmul]
  simp

/-- The geometric character comparison preserves the convolution point multiplication. -/
theorem geometricCharactersEquiv_mul (ψ χ : CartierDual K A →ₐ[K] L) :
    geometricCharactersEquiv K L A (ψ * χ) =
      geometricCharactersEquiv K L A ψ * geometricCharactersEquiv K L A χ := by
  apply MonoidHom.ext
  intro p
  apply Units.ext
  simp only [MonoidHom.mul_apply, Units.val_mul, geometricCharactersEquiv_apply]
  change scalarPointsEquiv K L (CartierDual K A) (ψ * χ) (geometricPointElement K L A p) = _
  rw [map_mul]
  change Algebra.TensorProduct.lift (scalarPointsEquiv K L (CartierDual K A) ψ)
    (scalarPointsEquiv K L (CartierDual K A) χ) (fun _ _ ↦ Commute.all _ _)
      (Coalgebra.comul (R := L) (geometricPointElement K L A p)) = _
  rw [geometricPointElement_comul, Algebra.TensorProduct.lift_tmul]
  rfl

/-- The full geometric point group of a Cartier dual is the character group
of the original full geometric point group. -/
def geometricCharactersMulEquiv :
    (CartierDual K A →ₐ[K] L) ≃* ((A →ₐ[K] L) →* Lˣ) :=
  { geometricCharactersEquiv K L A with map_mul' := geometricCharactersEquiv_mul K L A }

end HopfAlgebra.CartierDual

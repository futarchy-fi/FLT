/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudDualFaithful

/-!
# Integral bidual comparison and transpose

Evaluation gives the actual map from a model to its double dual. Transposition
then turns maps out of a model into maps into its dual, with the required inverse
identity on integral coordinates.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]

/-- The bidual map on models is inverse evaluation on coordinate rings. -/
def FF.toCartierBidual (X : FF R K) : ModelHom X X.cartierDual.cartierDual :=
  X.cartierBidualEquiv.symm.toBialgHom

/-- The actual bidual map is bijective on generic points. -/
theorem FF.genericHom_toCartierBidual_bijective (X : FF R K) :
    Function.Bijective (genericHom X.toCartierBidual) := by
  have inv (X Y : FF R K) (e : X.CoordinateRing ≃ₐc[R] Y.CoordinateRing)
      (x : X.Points) :
      genericHom e.toBialgHom (genericHom e.symm.toBialgHom x) = x := by
    rw [← genericHom_comp]
    have h : e.symm.toBialgHom.comp e.toBialgHom = BialgHom.id R X.CoordinateRing := by
      ext a
      exact e.symm_apply_apply a
    rw [h, genericHom_id]
  exact ⟨(Function.LeftInverse.injective (inv X _ X.cartierBidualEquiv)),
    (Function.RightInverse.surjective (inv _ X X.cartierBidualEquiv.symm))⟩

/-- Transpose a morphism into a dual using the actual integral bidual map. -/
def ModelHom.transpose {X Y : FF R K} (f : ModelHom X Y.cartierDual) :
    ModelHom Y X.cartierDual := Y.toCartierBidual.comp f.cartierDual

/-- Transposition recovers the prescribed original morphism after dualizing back. -/
theorem ModelHom.transpose_cartierDual {X Y : FF R K} (f : ModelHom X Y.cartierDual) :
    X.toCartierBidual.comp f.transpose.cartierDual = f := by
  apply DFunLike.ext
  intro φ
  change HopfAlgebra.CartierDual R Y.CoordinateRing at φ
  apply X.cartierBidualEquiv.injective
  change X.cartierBidualEquiv (X.cartierBidualEquiv.symm
    (HopfAlgebra.CartierDual.bialgMap f.transpose φ)) = X.cartierBidualEquiv (f φ)
  erw [BialgEquiv.apply_symm_apply]
  apply WithConv.ext
  apply LinearMap.ext
  intro ψ
  change HopfAlgebra.CartierDual R X.CoordinateRing at ψ
  change φ (Y.cartierBidualEquiv.symm (HopfAlgebra.CartierDual.bialgMap f ψ)) = ψ (f φ)
  have h := Y.cartierBidualEquiv.apply_symm_apply (HopfAlgebra.CartierDual.bialgMap f ψ)
  exact congrArg (fun q : HopfAlgebra.CartierDual R
    (HopfAlgebra.CartierDual R Y.CoordinateRing) ↦ q φ) h

end ThreeAdicPlan

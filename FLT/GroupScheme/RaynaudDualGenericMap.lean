/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCartierDual
public import FLT.GroupScheme.RaynaudGenericHopfMap

/-!
# Generic Cartier duality and integral restriction

Dual generic maps are defined by transposing their actual Hopf maps through
the base-change comparisons. Integral duality induces these prescribed maps.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]

/-- Transpose a generic map through the actual dual base-change comparisons. -/
def GenericGaloisHom.cartierDual {X Y : FF R K} (f : GenericGaloisHom X Y) :
    GenericGaloisHom Y.cartierDual X.cartierDual :=
  ofBialgHom (Y.cartierDualGenericEquiv.symm.toBialgHom.comp
    ((HopfAlgebra.CartierDual.bialgMap f.toBialgHom).comp
      X.cartierDualGenericEquiv.toBialgHom))

/-- The generic coordinates of a dual map are its conjugate transpose. -/
theorem GenericGaloisHom.toBialgHom_cartierDual {X Y : FF R K} (f : GenericGaloisHom X Y) :
    f.cartierDual.toBialgHom = Y.cartierDualGenericEquiv.symm.toBialgHom.comp
      ((HopfAlgebra.CartierDual.bialgMap f.toBialgHom).comp
        X.cartierDualGenericEquiv.toBialgHom) :=
  toBialgHom_ofBialgHom _

/-- The dual base-change comparison commutes with an integral morphism. -/
theorem ModelHom.cartierDual_baseChange {X Y : FF R K} (f : ModelHom X Y) :
    Y.cartierDualGenericEquiv.toBialgHom.comp f.cartierDual.baseChange =
      (HopfAlgebra.CartierDual.bialgMap f.baseChange).comp
        X.cartierDualGenericEquiv.toBialgHom := by
  apply DFunLike.ext
  intro z
  change K ⊗[R] HopfAlgebra.CartierDual R X.CoordinateRing at z
  change Y.cartierDualGenericEquiv (f.cartierDual.baseChange z) =
    HopfAlgebra.CartierDual.bialgMap f.baseChange (X.cartierDualGenericEquiv z)
  induction z using TensorProduct.inductionOn with
  | tmul l φ =>
    apply WithConv.ext
    apply (TensorProduct.isBaseChange R Y.CoordinateRing K).algHom_ext
    intro y
    change HopfAlgebra.CartierDual.baseChangeAlgEquiv K
      (l ⊗ₜ[R] HopfAlgebra.CartierDual.bialgMap f φ) (1 ⊗ₜ[R] y) =
      HopfAlgebra.CartierDual.baseChangeAlgEquiv K (l ⊗ₜ[R] φ) (1 ⊗ₜ[R] f y)
    simp
  | add z w hz hw =>
    exact (map_add (Y.cartierDualGenericEquiv.toBialgHom.comp f.cartierDual.baseChange) z w).trans
      ((congrArg₂ (· + ·) hz hw).trans (map_add
        ((HopfAlgebra.CartierDual.bialgMap f.baseChange).comp
          X.cartierDualGenericEquiv.toBialgHom) z w).symm)

/-- Restricting an integral dual morphism gives the dual prescribed generic map. -/
@[simp] theorem ModelHom.genericHom_cartierDual {X Y : FF R K} (f : ModelHom X Y) :
    genericHom f.cartierDual = (genericHom f).cartierDual := by
  apply GenericGaloisHom.toBialgHom_inj
  rw [ModelHom.toBialgHom_genericHom, GenericGaloisHom.toBialgHom_cartierDual,
    ModelHom.toBialgHom_genericHom]
  apply DFunLike.ext
  intro z
  apply Y.cartierDualGenericEquiv.injective
  change Y.cartierDualGenericEquiv (f.cartierDual.baseChange z) =
    Y.cartierDualGenericEquiv (Y.cartierDualGenericEquiv.symm
      (HopfAlgebra.CartierDual.bialgMap f.baseChange (X.cartierDualGenericEquiv z)))
  rw [BialgEquiv.apply_symm_apply]
  exact DFunLike.congr_fun f.cartierDual_baseChange z

end ThreeAdicPlan

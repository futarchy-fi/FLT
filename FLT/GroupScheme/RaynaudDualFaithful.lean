/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudDualGenericMap

/-!
# Faithfulness and generic isomorphisms under Cartier duality

Perfect dual evaluation recovers a generic map from its transpose. Transposing
an inverse Hopf map proves that generic isomorphisms remain isomorphisms.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]

/-- Generic Cartier duality is faithful. -/
theorem GenericGaloisHom.cartierDual_injective {X Y : FF R K} :
    Function.Injective (cartierDual (X := X) (Y := Y)) := by
  intro f g h
  apply toBialgHom_inj
  apply DFunLike.ext
  intro a
  apply (HopfAlgebra.CartierDual.bidualEquiv (R := K)).injective
  apply WithConv.ext
  apply LinearMap.ext
  intro φ
  have ht := congrArg toBialgHom h
  rw [toBialgHom_cartierDual, toBialgHom_cartierDual] at ht
  have hv := congrArg (fun q ↦ Y.cartierDualGenericEquiv
    (q (X.cartierDualGenericEquiv.symm φ))) ht
  change Y.cartierDualGenericEquiv (Y.cartierDualGenericEquiv.symm
    (HopfAlgebra.CartierDual.bialgMap f.toBialgHom
      (X.cartierDualGenericEquiv (X.cartierDualGenericEquiv.symm φ)))) =
    Y.cartierDualGenericEquiv (Y.cartierDualGenericEquiv.symm
    (HopfAlgebra.CartierDual.bialgMap g.toBialgHom
      (X.cartierDualGenericEquiv (X.cartierDualGenericEquiv.symm φ)))) at hv
  simp only [BialgEquiv.apply_symm_apply] at hv
  exact congrArg (fun ψ : HopfAlgebra.CartierDual K (K ⊗[R] Y.CoordinateRing) ↦ ψ a) hv

/-- Duality preserves bijectivity on the specified generic point groups. -/
theorem GenericGaloisHom.cartierDual_bijective {X Y : FF R K} (f : GenericGaloisHom X Y)
    (hf : Function.Bijective f) : Function.Bijective f.cartierDual := by
  let e := BialgEquiv.ofBijective f.toBialgHom
    ⟨f.toBialgHom_injective hf.2, f.toBialgHom_surjective hf.1⟩
  let d := HopfAlgebra.CartierDual.bialgMap e.toBialgHom
  let i := HopfAlgebra.CartierDual.bialgMap e.symm.toBialgHom
  have hi : Function.LeftInverse i d := by
    intro φ
    apply WithConv.ext
    apply LinearMap.ext
    intro a
    change φ (e (e.symm a)) = φ a
    rw [e.apply_symm_apply]
  have hd : Function.RightInverse i d := by
    intro φ
    apply WithConv.ext
    apply LinearMap.ext
    intro a
    change φ (e.symm (e a)) = φ a
    rw [e.symm_apply_apply]
  let de := BialgEquiv.ofBijective d ⟨hi.injective, hd.surjective⟩
  exact ofBialgHom_bijective
    ((X.cartierDualGenericEquiv.trans de).trans Y.cartierDualGenericEquiv.symm)

end ThreeAdicPlan

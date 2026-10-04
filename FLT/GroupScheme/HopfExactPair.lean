/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.IntegralSubquotientExtension
public import FLT.GroupScheme.CartierDualInvariants

/-! # Torsor descent for an actual augmentation-kernel presentation -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace HopfAlgebra.ExactPair
variable {R A H Q : Type} [CommRing R] [CommRing A] [CommRing H] [CommRing Q]
  [HopfAlgebra R A] [HopfAlgebra R H] [HopfAlgebra R Q]
  (i : H →ₐc[R] A) (q : Q →ₐc[R] H) (hi : Function.Surjective i)
  (hk : augmentationIdeal q = RingHom.ker i.toAlgHom.toRingHom)

/-- The actual kernel presentation identifies its quotient with the specified kernel. -/
def kernelEquiv : (H ⧸ augmentationIdeal q) ≃ₐ[R] A :=
  (Ideal.quotientEquivAlgOfEq R hk).trans (Ideal.quotientKerAlgEquivOfSurjective hi)

/-- The kernel identification uses the original inclusion. -/
@[simp] theorem kernelEquiv_mk (h : H) : kernelEquiv i q hi hk (Ideal.Quotient.mk _ h) = i h := rfl

include hi hk in
/-- Kernel exactness forces the original composite to be the zero group map. -/
theorem compositionZero : i.toAlgHom.comp q.toAlgHom =
    (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R Q) := by
  ext b
  have he := congrArg (kernelEquiv i q hi hk)
    (AlgHom.congr_fun (quotient_comp_bialgHom q) b)
  change kernelEquiv i q hi hk (Ideal.Quotient.mk _ (q b)) =
    kernelEquiv i q hi hk (algebraMap R _ (Coalgebra.counit b)) at he
  rw [kernelEquiv_mk, AlgEquiv.commutes] at he
  exact he

variable [Algebra Q H] [IsScalarTower R Q H]
  (hq : q.toAlgHom = IsScalarTower.toAlgHom R Q H)

/-- The canonical torsor retains the specified kernel algebra. -/
def torsor : H ⊗[Q] H ≃ₐ[H] H ⊗[R] A :=
  (torsorEquiv q hq).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : H ≃ₐ[H] H) (kernelEquiv i q hi hk))

/-- The second torsor coordinate is the original kernel coaction. -/
theorem torsor_second (h : H) : torsor i q hi hk hq (1 ⊗ₜ[Q] h) =
    Algebra.TensorProduct.map (AlgHom.id R H) i.toAlgHom (Coalgebra.comul h) := by
  change (Algebra.TensorProduct.congr (AlgEquiv.refl : H ≃ₐ[H] H) (kernelEquiv i q hi hk))
    (torsorHom q hq (1 ⊗ₜ[Q] h)) = _
  simp only [torsorHom, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  change Algebra.TensorProduct.map (AlgHom.id R H) (kernelEquiv i q hi hk).toAlgHom
    (Algebra.TensorProduct.map (AlgHom.id R H) (Ideal.Quotient.mkₐ R (augmentationIdeal q))
      (Coalgebra.comul h)) = _
  generalize Coalgebra.comul (R := R) h = t
  induction t using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable [Module.FaithfullyFlat Q H]

include hi hk hq in
/-- Faithfully flat descent characterizes original quotient coordinates by invariance. -/
theorem exists_preimage_iff (h : H) : (∃ b, q b = h) ↔
    Algebra.TensorProduct.map (AlgHom.id R H) i.toAlgHom (Coalgebra.comul h) =
      h ⊗ₜ[R] (1 : A) := by
  have hex := Algebra.IsEffective.of_faithfullyFlat Q H
  have he : (q : Q → H) = algebraMap Q H := congrArg DFunLike.coe hq
  change (h ∈ Set.range q) ↔ _
  rw [he]
  change (h ∈ Set.range (Algebra.linearMap Q H)) ↔ _
  rw [← hex h, Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero]
  constructor
  · intro hh
    rw [← torsor_second i q hi hk hq, ← hh]
    exact (torsor i q hi hk hq).commutes h
  · intro hh
    apply (torsor i q hi hk hq).injective
    rw [torsor_second, hh]
    exact (torsor i q hi hk hq).commutes h

end HopfAlgebra.ExactPair

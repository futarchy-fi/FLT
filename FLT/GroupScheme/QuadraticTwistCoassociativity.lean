/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.QuadraticTwistIdentities

/-!
# Coassociativity of quadratic descent

Tensor comparison respects maps and reassociation, so coassociativity descends
from the original Hopf algebra.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

open scoped TensorProduct

namespace QuadraticTwist

universe v
variable {R S A B C E : Type v}
variable [CommRing R] [CommRing S] [CommRing A] [CommRing B] [CommRing C] [CommRing E]
variable [Algebra R S] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R E]

/-- Combining coefficients commutes with maps in either tensor factor. -/
theorem tensorBaseChange_map (f : A →ₐ[R] C) (g : B →ₐ[R] E)
    (x : S ⊗[R] A) (y : S ⊗[R] B) :
    tensorBaseChange R S C E
      (Algebra.TensorProduct.map (AlgHom.id R S) f x ⊗ₜ[S]
        Algebra.TensorProduct.map (AlgHom.id R S) g y) =
      Algebra.TensorProduct.map (AlgHom.id R S) (Algebra.TensorProduct.map f g)
        (tensorBaseChange R S A B (x ⊗ₜ[S] y)) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, TensorProduct.add_tmul, hx, hx']
  | tmul s a =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, TensorProduct.tmul_add, hy, hy']
    | tmul t b => rfl

/-- Combining three coefficients respects the tensor associator. -/
theorem tensorBaseChange_assoc (x : S ⊗[R] A) (y : S ⊗[R] B)
    (z : S ⊗[R] C) :
    tensorBaseChange R S A (B ⊗[R] C)
      (x ⊗ₜ[S] tensorBaseChange R S B C (y ⊗ₜ[S] z)) =
      Algebra.TensorProduct.map (AlgHom.id R S)
        (Algebra.TensorProduct.assoc R R R A B C).toAlgHom
        (tensorBaseChange R S (A ⊗[R] B) C
          (tensorBaseChange R S A B (x ⊗ₜ[S] y) ⊗ₜ[S] z)) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, TensorProduct.add_tmul, hx, hx']
  | tmul s a =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, TensorProduct.add_tmul,
        TensorProduct.tmul_add, hy, hy']
    | tmul t b =>
      induction z using TensorProduct.inductionOn with
      | add z z' hz hz' => simp only [map_add, TensorProduct.tmul_add, hz, hz']
      | tmul w c => simp [mul_assoc]

/-- Tensor products of involutions are involutions. -/
theorem tensor_involutive (ι : A ≃ₐ[R] A) (κ : B ≃ₐ[R] B)
    (hι : Function.Involutive ι) (hκ : Function.Involutive κ) :
    Function.Involutive (Algebra.TensorProduct.congr ι κ) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => simp [hι a, hκ b]

end QuadraticTwist

namespace QuadraticTwist

universe v
variable {R H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable (u : Rˣ) (r : R) (hr : 2 * r = 1)

local notation "ι" => HopfAlgebra.antipodeAlgEquiv R H
local notation "hι" => HopfAlgebra.antipode_involutive R H
local notation "ι₂" => Algebra.TensorProduct.congr ι ι
local notation "hι₂" => tensor_involutive ι ι hι hι
local notation "D" => model (u : R) ι
local notation "S" => QuadraticAlgebra R (u : R) 0
local notation "e₂" => modelTensorEquiv ι ι u hι hι r hr
local notation "eR" => modelTensorEquiv ι ι₂ u hι hι₂ r hr
local notation "eL" => modelTensorEquiv ι₂ ι u hι₂ hι r hr

/-- Tensor comparison for the right-associated cube of the fixed model. -/
noncomputable def modelTensorRightEquiv :
    D ⊗[R] (D ⊗[R] D) ≃ₐ[R] model (u : R) (Algebra.TensorProduct.congr ι ι₂) :=
  (Algebra.TensorProduct.congr AlgEquiv.refl e₂).trans eR

/-- Tensor comparison for the left-associated cube of the fixed model. -/
noncomputable def modelTensorLeftEquiv :
    (D ⊗[R] D) ⊗[R] D ≃ₐ[R] model (u : R) (Algebra.TensorProduct.congr ι₂ ι) :=
  (Algebra.TensorProduct.congr e₂ AlgEquiv.refl).trans eL

/-- The right-associated comparison on a pure outer tensor. -/
theorem modelTensorRightEquiv_tmul (a : D) (z : D ⊗[R] D) :
    (modelTensorRightEquiv (H := H) u r hr (a ⊗ₜ[R] z)).val =
      tensorBaseChange R S H (H ⊗[R] H) (a.val ⊗ₜ[S] (e₂ z).val) := by
  exact modelTensorEquiv_tmul ι ι₂ u hι hι₂ r hr a (e₂ z)

/-- The left-associated comparison on a pure outer tensor. -/
theorem modelTensorLeftEquiv_tmul (z : D ⊗[R] D) (a : D) :
    (modelTensorLeftEquiv (H := H) u r hr (z ⊗ₜ[R] a)).val =
      tensorBaseChange R S (H ⊗[R] H) H ((e₂ z).val ⊗ₜ[S] a.val) := by
  exact modelTensorEquiv_tmul ι₂ ι u hι₂ hι r hr (e₂ z) a

/-- The two fixed tensor-cube comparisons respect reassociation. -/
theorem modelTensor_assoc (z : (D ⊗[R] D) ⊗[R] D) :
    (modelTensorRightEquiv (H := H) u r hr
      (Algebra.TensorProduct.assoc R R R D D D z)).val =
    Algebra.TensorProduct.map (AlgHom.id R S)
      (Algebra.TensorProduct.assoc R R R H H H).toAlgHom
      (modelTensorLeftEquiv (H := H) u r hr z).val := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
  | tmul z c =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, Subalgebra.coe_add, hx, hy]
    | tmul a b =>
      rw [Algebra.TensorProduct.assoc_tmul, modelTensorRightEquiv_tmul,
        modelTensorLeftEquiv_tmul, modelTensorEquiv_tmul, modelTensorEquiv_tmul]
      exact tensorBaseChange_assoc a.val b.val c.val

variable [Coalgebra.IsCocomm R H]

/-- Comparing a comultiplication in the right tensor factor recovers the original map. -/
theorem modelTensorRight_comul (z : D ⊗[R] D) :
    (modelTensorRightEquiv (H := H) u r hr
      (Algebra.TensorProduct.map (AlgHom.id R D) (comul u r hr) z)).val =
    Algebra.TensorProduct.map (AlgHom.id R S)
      (Algebra.TensorProduct.map (AlgHom.id R H) (Bialgebra.comulAlgHom R H))
      (e₂ z).val := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, modelTensorRightEquiv_tmul,
      comul_compat, modelTensorEquiv_tmul]
    simpa using tensorBaseChange_map (AlgHom.id R H) (Bialgebra.comulAlgHom R H) a.val b.val

/-- Comparing a comultiplication in the left tensor factor recovers the original map. -/
theorem modelTensorLeft_comul (z : D ⊗[R] D) :
    (modelTensorLeftEquiv (H := H) u r hr
      (Algebra.TensorProduct.map (comul u r hr) (AlgHom.id R D) z)).val =
    Algebra.TensorProduct.map (AlgHom.id R S)
      (Algebra.TensorProduct.map (Bialgebra.comulAlgHom R H) (AlgHom.id R H))
      (e₂ z).val := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, modelTensorLeftEquiv_tmul,
      comul_compat, modelTensorEquiv_tmul]
    simpa using tensorBaseChange_map (Bialgebra.comulAlgHom R H) (AlgHom.id R H) a.val b.val

/-- The descended comultiplication is coassociative. -/
theorem comul_coassoc :
    (Algebra.TensorProduct.assoc R R R D D D).toAlgHom.comp
      ((Algebra.TensorProduct.map (comul u r hr) (AlgHom.id R D)).comp (comul u r hr)) =
      (Algebra.TensorProduct.map (AlgHom.id R D) (comul u r hr)).comp (comul u r hr) := by
  apply AlgHom.ext
  intro a
  apply (modelTensorRightEquiv (H := H) u r hr).injective
  apply Subtype.ext
  change (modelTensorRightEquiv (H := H) u r hr
    (Algebra.TensorProduct.assoc R R R D D D
      (Algebra.TensorProduct.map (comul u r hr) (AlgHom.id R D) (comul u r hr a)))).val = _
  simp only [AlgHom.comp_apply]
  rw [modelTensor_assoc, modelTensorLeft_comul, modelTensorRight_comul, comul_compat]
  have h : (Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
      ((Algebra.TensorProduct.map (Bialgebra.comulAlgHom R H) (AlgHom.id R H)).comp
        (Bialgebra.comulAlgHom R H)) =
      (Algebra.TensorProduct.map (AlgHom.id R H) (Bialgebra.comulAlgHom R H)).comp
        (Bialgebra.comulAlgHom R H) := by
    apply AlgHom.ext
    exact Coalgebra.coassoc_apply
  simp only [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_id_comp, h]

/-- The quadratic inversion twist inherits a Hopf algebra structure. -/
@[instance_reducible]
noncomputable def hopfAlgebra : HopfAlgebra R D :=
  hopfAlgebraOfCoassoc u r hr (comul_coassoc u r hr)

end QuadraticTwist

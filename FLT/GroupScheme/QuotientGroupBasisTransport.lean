/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.GroupLikeBasisTransport
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Group-like bases on a coordinate quotient

When a coordinate quotient identifies with an integral Hopf kernel, the
transported basis satisfies exactly the diagonal compatibility used by the
canonical fibre torsor. No coalgebra structure on the quotient is assumed.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace CoactionBasis

variable {R A H G : Type*} [CommRing R] [CommRing A] [CommRing H]
  [Bialgebra R A] [Bialgebra R H] [CommGroup G]
  (I : Ideal A) (e : (A ⧸ I) ≃ₐ[R] H) (j : A →ₐc[R] H)
  (hj : ∀ a, e (Ideal.Quotient.mk I a) = j a)
  (d : MonoidAlgebra R G ≃ₐc[R] H)

/-- Transport the actual kernel basis to the quotient used by the torsor. -/
def quotientGroupBasis : Module.Basis G R (A ⧸ I) :=
  (transportedGroupBasis d).map e.symm.toLinearEquiv

/-- The quotient basis has the correct identity degree. -/
theorem quotientGroupBasis_one : quotientGroupBasis I e d 1 = 1 := by
  simp [quotientGroupBasis, transportedGroupBasis_one]

/-- The quotient basis respects the group operation. -/
theorem quotientGroupBasis_mul (i k : G) :
    quotientGroupBasis I e d (i * k) = quotientGroupBasis I e d i * quotientGroupBasis I e d k := by
  simp [quotientGroupBasis, transportedGroupBasis_mul]

include hj in
/-- The quotient diagonal is induced by the original middle comultiplication. -/
theorem quotientGroupBasis_diagonal :
    diagonal (quotientGroupBasis I e d) ∘ₗ (Ideal.Quotient.mkₐ R I).toLinearMap =
      TensorProduct.map (Ideal.Quotient.mkₐ R I).toLinearMap
        (Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ Coalgebra.comul := by
  have he : e.toLinearMap ∘ₗ (Ideal.Quotient.mkₐ R I).toLinearMap = j.toLinearMap := by
    ext a
    exact hj a
  have hd : TensorProduct.map e.toLinearMap e.toLinearMap ∘ₗ
      diagonal (quotientGroupBasis I e d) = Coalgebra.comul ∘ₗ e.toLinearMap := by
    apply (quotientGroupBasis I e d).ext
    intro i
    simp only [LinearMap.comp_apply, diagonal_basis, TensorProduct.map_tmul]
    have hb : e (quotientGroupBasis I e d i) = transportedGroupBasis d i := by
      simp [quotientGroupBasis]
    change e (quotientGroupBasis I e d i) ⊗ₜ[R] e (quotientGroupBasis I e d i) =
      Coalgebra.comul (e (quotientGroupBasis I e d i))
    rw [hb, (transportedGroupBasis_groupLike d i).comul_eq_tmul_self]
  apply LinearMap.ext
  intro a
  apply (TensorProduct.congr e.toLinearEquiv e.toLinearEquiv).injective
  change (TensorProduct.map e.toLinearMap e.toLinearMap ∘ₗ
    (diagonal (quotientGroupBasis I e d) ∘ₗ (Ideal.Quotient.mkₐ R I).toLinearMap)) a =
    (TensorProduct.map e.toLinearMap e.toLinearMap ∘ₗ
      (TensorProduct.map (Ideal.Quotient.mkₐ R I).toLinearMap
        (Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ Coalgebra.comul)) a
  rw [← LinearMap.comp_assoc, hd, LinearMap.comp_assoc, he,
    ← LinearMap.comp_assoc, ← TensorProduct.map_comp, he]
  exact (CoalgHomClass.map_comp_comul_apply j a).symm

end CoactionBasis

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-! # Coordinates in the localized residue-fibre quotient comparison -/

@[expose] public noncomputable section

open scoped TensorProduct
open Algebra.TensorProduct

namespace Ideal.Fiber

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (p : Ideal R) [p.IsPrime] (q : Ideal (p.Fiber S)) [q.IsPrime]

/-- The localized fibre comparison preserves the original algebra coordinates. -/
theorem algEquivAux₂_algebraMap_one_tmul (s : S) : algEquivAux₂ p q
    (algebraMap (p.Fiber S) (Localization.AtPrime q) (1 ⊗ₜ[R] s)) =
      Ideal.Quotient.mk _ (algebraMap S _ s) := by
  let : Algebra S (p.Fiber S) := rightAlgebra
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let pS := p.map (algebraMap R S)
  let r := q.comap (includeRight : S →ₐ[R] p.Fiber S)
  let Sr := Localization.AtPrime r
  let e₁ := Ideal.Fiber.algEquivAux₁ (S := S) p
  let q' := q.comap e₁.symm
  have : (q'.under (S ⧸ pS)).LiesOver r :=
    Ideal.under_liesOver_of_liesOver (S ⧸ pS) q' (q.under S)
  have he : Algebra.algebraMapSubmonoid (S ⧸ pS) r.primeCompl =
      (q'.under (S ⧸ pS)).primeCompl :=
    Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective
      (q'.under (S ⧸ pS)) r Ideal.Quotient.mk_surjective
  have : IsLocalization (Algebra.algebraMapSubmonoid (S ⧸ pS) r.primeCompl)
      (Localization.AtPrime q') := by
    rw [he]
    exact IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid (S ⧸ pS)
        (Algebra.algebraMapSubmonoid S p.primeCompl)) (Localization.AtPrime q') q'
  have := IsScalarTower.to₁₃₄ R S (S ⧸ pS) (Localization.AtPrime q')
  have := IsScalarTower.to₁₃₄ R S (S ⧸ pS) (Sr ⧸ pS.map (algebraMap S Sr))
  unfold Ideal.Fiber.algEquivAux₂
  change ((Localization.localAlgEquiv q' q e₁.symm rfl).symm.trans
    ((IsLocalization.algEquiv
      (Algebra.algebraMapSubmonoid (S ⧸ pS) r.primeCompl)
      (Localization.AtPrime q') (Sr ⧸ pS.map (algebraMap S Sr))).restrictScalars S))
        (algebraMap S _ s) = algebraMap S _ s
  exact AlgEquiv.commutes _ s

/-- The fibre at a specified point, reduced by the extended original base ideal. -/
def localizedQuotientEquiv :
    Localization.AtPrime q ≃ₐ[R]
      Localization.AtPrime (q.comap includeRight) ⧸
        p.map (algebraMap R (Localization.AtPrime (q.comap includeRight))) :=
  (algEquivAux₂ p q).trans (Ideal.quotientEquivAlgOfEq R (Ideal.map_map _ _))

@[simp] theorem localizedQuotientEquiv_algebraMap_one_tmul (s : S) :
    localizedQuotientEquiv p q
      (algebraMap (p.Fiber S) (Localization.AtPrime q) (1 ⊗ₜ[R] s)) =
        Ideal.Quotient.mk _ (algebraMap S _ s) := by
  rw [localizedQuotientEquiv, AlgEquiv.trans_apply, algEquivAux₂_algebraMap_one_tmul]
  rfl

/-- Choose the original prime explicitly, using its verified contraction equality. -/
def localizedQuotientEquivOfEq (P : Ideal S) [P.IsPrime]
    (hP : q.comap includeRight = P) :
    Localization.AtPrime q ≃ₐ[R]
      Localization.AtPrime P ⧸ p.map (algebraMap R (Localization.AtPrime P)) := by
  subst P
  exact localizedQuotientEquiv p q

@[simp] theorem localizedQuotientEquivOfEq_algebraMap_one_tmul
    (P : Ideal S) [P.IsPrime] (hP : q.comap includeRight = P) (s : S) :
    localizedQuotientEquivOfEq p q P hP
      (algebraMap (p.Fiber S) (Localization.AtPrime q) (1 ⊗ₜ[R] s)) =
        Ideal.Quotient.mk _ (algebraMap S _ s) := by
  subst P
  exact localizedQuotientEquiv_algebraMap_one_tmul p q s

end Ideal.Fiber

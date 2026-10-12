/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianOverlapPolynomial
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Principal affine Grassmannian overlaps

Localizing the chart polynomial ring at the second-basis determinant represents
exactly those original quotient points lying in both charts. No quotient equation
is discarded by passing to this principal open.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.GrassmannianChart
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {d : ℕ}
  (P : Matrix (Fin d) (Fin d) R) (Q : Matrix ι (Fin d) R)

/-- The coordinate ring of the determinant principal overlap. -/
abbrev principalOverlapRing := Localization.Away (overlapPolynomial P Q)

variable {S : Type*} [CommRing S] [Algebra R S]

/-- The universal property of the principal localization, as coefficient algebra maps. -/
def principalOverlapHomEquiv :
    (principalOverlapRing P Q →ₐ[R] S) ≃
      {f : MvPolynomial (Fin d × ι) R →ₐ[R] S // IsUnit (f (overlapPolynomial P Q))} where
  toFun f := ⟨f.comp (Algebra.algHom R _ _),
    (IsLocalization.Away.algebraMap_isUnit (overlapPolynomial P Q)).map f⟩
  invFun f := IsLocalization.Away.liftAlgHom (overlapPolynomial P Q) f.property
  left_inv f := by
    apply IsLocalization.algHom_ext (Submonoid.powers (overlapPolynomial P Q))
    apply AlgHom.ext
    intro x
    simp [Algebra.algHom, IsLocalization.Away.liftAlgHom]
  right_inv f := by
    apply Subtype.ext
    apply AlgHom.ext
    intro x
    simp [Algebra.algHom, IsLocalization.Away.liftAlgHom]

/-- The actual quotient-chart points for which the second summand is also a quotient basis. -/
def PrincipalOverlapPoints :=
  {N : SplitChart S (ι → S) d // Function.Bijective (N.val.toSubmodule.mkQ.comp
    (matrixSelectedSummand (P.map (algebraMap R S)) (Q.map (algebraMap R S))))}

/-- Determinant-localized algebra maps classify exactly the original overlap quotient points. -/
def principalOverlapPointEquiv :
    (principalOverlapRing P Q →ₐ[R] S) ≃ PrincipalOverlapPoints (S := S) P Q :=
  (principalOverlapHomEquiv P Q).trans
    { toFun := fun f ↦ ⟨splitChartPolynomialEquiv R S ι d f.val,
        (overlapPolynomial_isUnit_iff P Q f.val).mp f.property⟩
      invFun := fun N ↦ ⟨(splitChartPolynomialEquiv R S ι d).symm N.val, by
        apply (overlapPolynomial_isUnit_iff P Q _).mpr
        rw [(splitChartPolynomialEquiv R S ι d).apply_symm_apply]
        exact N.property⟩
      left_inv := fun f ↦ Subtype.ext ((splitChartPolynomialEquiv R S ι d).symm_apply_apply f.val)
      right_inv := fun N ↦
        Subtype.ext ((splitChartPolynomialEquiv R S ι d).apply_symm_apply N.val) }

/-- Each original overlap point has a unique localized classifying algebra map. -/
theorem principalOverlapPoint_unique (N : PrincipalOverlapPoints (S := S) P Q) :
    ∃! f : principalOverlapRing P Q →ₐ[R] S, principalOverlapPointEquiv P Q f = N :=
  (principalOverlapPointEquiv P Q).bijective.existsUnique N

end FLT.Mazur.GrassmannianChart

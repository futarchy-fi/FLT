/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.GlobalModel
public import FLT.GroupScheme.PadicLocalPresentation
public import FLT.GroupScheme.RaynaudExtension

/-! # Localized presentations of finite flat models over the 3-adic integers -/

@[expose] public noncomputable section

namespace ThreeAdicPlan

open MvPolynomial

/-- The coordinate ring of a local finite flat 3-adic model is a localized
polynomial quotient with one relation per special-fibre cotangent coordinate. -/
theorem FF.exists_minimal_local_presentation (X : FF ℤ_[3] ℚ_[3])
    [IsLocalRing X.CoordinateRing] :
    ∃ P : Algebra.Generators ℤ_[3] X.CoordinateRing
        (Fin (HopfAlgebra.padicSpecialFiberCotangentDimension 3 X.CoordinateRing)),
      let f := aeval (R := ℤ_[3]) P.val
      ∃ (g : Fin (HopfAlgebra.padicSpecialFiberCotangentDimension 3 X.CoordinateRing) →
          f.localizedSource)
        (e : (f.localizedSource ⧸ Ideal.span (Set.range g)) ≃ₐ[ℤ_[3]] X.CoordinateRing),
        ∀ s, e (Ideal.Quotient.mk _ s) = f.localizeAtMaximal s :=
  HopfAlgebra.exists_minimal_local_padic_presentation 3 X.CoordinateRing

/-- A chosen local finite flat model of a Galois module over the 3-adic integers
has a minimal localized square presentation of its coordinate ring. -/
theorem HasFiniteFlatModel.exists_minimal_local_presentation
    {W : FiniteContinuousGaloisModule ℚ_[3]} (M : HasFiniteFlatModel ℤ_[3] W)
    [IsLocalRing M.CoordinateRing] :
    ∃ P : Algebra.Generators ℤ_[3] M.CoordinateRing
        (Fin (HopfAlgebra.padicSpecialFiberCotangentDimension 3 M.CoordinateRing)),
      let f := aeval (R := ℤ_[3]) P.val
      ∃ (g : Fin (HopfAlgebra.padicSpecialFiberCotangentDimension 3 M.CoordinateRing) →
          f.localizedSource)
        (e : (f.localizedSource ⧸ Ideal.span (Set.range g)) ≃ₐ[ℤ_[3]] M.CoordinateRing),
        ∀ s, e (Ideal.Quotient.mk _ s) = f.localizeAtMaximal s :=
  HopfAlgebra.exists_minimal_local_padic_presentation 3 M.CoordinateRing

end ThreeAdicPlan

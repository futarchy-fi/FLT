/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.FractionalPrincipalGraded
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! # Multiplication on the actual integer principal graded quotients -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {t : R}

/-- The degree-adding product in residue coordinates. Its field formula is proved below. -/
def fractionalPrincipalGradedMul (ht : t ≠ 0) (m n : ℤ)
    (x : FractionalPrincipalGradedPiece (K := K) t m)
    (y : FractionalPrincipalGradedPiece (K := K) t n) :
    FractionalPrincipalGradedPiece (K := K) t (m + n) :=
  fractionalPrincipalGradedEquiv (K := K) ht (m + n)
    ((fractionalPrincipalGradedEquiv (K := K) ht m).symm x *
      (fractionalPrincipalGradedEquiv (K := K) ht n).symm y)

/-- Multiplying coefficient representatives multiplies their actual coefficients. -/
theorem fractionalPrincipalGradedMul_representative (ht : t ≠ 0) (m n : ℤ) (a b : R) :
    fractionalPrincipalGradedMul (K := K) ht m n
      ((fractionalPrincipalNext (K := K) t m).mkQ (fractionalPrincipalEquiv (K := K) ht m a))
      ((fractionalPrincipalNext (K := K) t n).mkQ (fractionalPrincipalEquiv (K := K) ht n b)) =
      (fractionalPrincipalNext (K := K) t (m + n)).mkQ
        (fractionalPrincipalEquiv (K := K) ht (m + n) (a * b)) := by
  rw [← fractionalPrincipalGradedEquiv_mk, ← fractionalPrincipalGradedEquiv_mk,
    ← fractionalPrincipalGradedEquiv_mk]
  unfold fractionalPrincipalGradedMul
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  rfl

/-- The coordinate-defined product is induced by actual multiplication in the fraction field. -/
theorem fractionalPrincipalGradedMul_mk (ht : t ≠ 0) (m n : ℤ)
    (x : fractionalPrincipalFiltration (K := K) t m)
    (y : fractionalPrincipalFiltration (K := K) t n) :
    fractionalPrincipalGradedMul (K := K) ht m n
      ((fractionalPrincipalNext (K := K) t m).mkQ x)
      ((fractionalPrincipalNext (K := K) t n).mkQ y) =
      (fractionalPrincipalNext (K := K) t (m + n)).mkQ
        ⟨(x : K) * y, fractionalPrincipalFiltration_mul_mem t ht m n x.property y.property⟩ := by
  obtain ⟨a, rfl⟩ := (fractionalPrincipalEquiv (K := K) ht m).surjective x
  obtain ⟨b, rfl⟩ := (fractionalPrincipalEquiv (K := K) ht n).surjective y
  rw [fractionalPrincipalGradedMul_representative]
  congr 1
  apply Subtype.ext
  simp only [fractionalPrincipalEquiv_coe, map_mul]
  rw [zpow_add₀ ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ht)]
  ring

/-- Residue coordinates turn the degree-adding product into residue multiplication. -/
theorem fractionalPrincipalGradedMul_coordinate (ht : t ≠ 0) (m n : ℤ)
    (x : FractionalPrincipalGradedPiece (K := K) t m)
    (y : FractionalPrincipalGradedPiece (K := K) t n) :
    (fractionalPrincipalGradedEquiv (K := K) ht (m + n)).symm
      (fractionalPrincipalGradedMul (K := K) ht m n x y) =
      (fractionalPrincipalGradedEquiv (K := K) ht m).symm x *
        (fractionalPrincipalGradedEquiv (K := K) ht n).symm y :=
  LinearEquiv.symm_apply_apply _ _

end PadicHodgeTheory

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatDifferentials
public import FLT.GroupScheme.LocalDifferentBounds
public import FLT.Mathlib.RingTheory.AugmentationGenerators
public import FLT.Mathlib.RingTheory.PresentationJacobianBound

/-!
# Minimal coordinates and the square-presentation Jacobian bound

A local finite flat model admits polynomial generators indexed by the
dimension of its residual invariant cotangent module. For any genuine square
presentation of a killed-by-three model, its Jacobian determinant divides
`3 ^ n`; at every integral point its normalized valuation is at most `n`.

These are two separate assertions. Existence of a square presentation for
every model still requires the special-fibre complete-intersection theorem.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open MvPolynomial

namespace ThreeAdicPlan

/-- The augmentation ideal in the coordinate ring of a finite flat model. -/
abbrev FF.augmentationIdeal (M : FF ℤ_[3] ℚ_[3]) : Ideal M.CoordinateRing :=
  RingHom.ker (Bialgebra.counitAlgHom ℤ_[3] M.CoordinateRing)

/-- The number of coordinates in a minimal local presentation, computed
from the invariant cotangent module at the identity. -/
abbrev FF.embeddingDimension (M : FF ℤ_[3] ℚ_[3]) : ℕ :=
  Module.finrank (IsLocalRing.ResidueField ℤ_[3])
    ((IsLocalRing.ResidueField ℤ_[3]) ⊗[ℤ_[3]] M.augmentationIdeal.Cotangent)

/-- Local finite flat coordinate rings have a polynomial surjection with
the minimal cotangent number of variables, all vanishing at the identity. -/
theorem FF.exists_minimal_polynomial_generators (M : FF ℤ_[3] ℚ_[3])
    [IsLocalRing M.CoordinateRing] :
    ∃ P : Algebra.Generators ℤ_[3] M.CoordinateRing (Fin M.embeddingDimension),
      ∀ i, P.val i ∈ M.augmentationIdeal := by
  obtain ⟨P, hP, _⟩ :=
    (Bialgebra.counitAlgHom ℤ_[3] M.CoordinateRing).exists_minimal_augmentation_generators
  exact ⟨P, hP⟩

/-- For a generating square presentation of a killed-by-three model, the
Jacobian determinant divides `3 ^ n` in the coordinate algebra. -/
theorem FF.jacobian_det_dvd_three_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : FF ℤ_[3] ℚ_[3]) (hM : KilledBy 3 M)
    (P : Algebra.Presentation ℤ_[3] M.CoordinateRing ι ι) :
    Matrix.det (fun i j ↦ aeval P.val (pderiv j (P.relation i))) ∣
      (3 : M.CoordinateRing) ^ Fintype.card ι := by
  simpa only [map_ofNat] using P.jacobian_det_dvd_pow 3
    (M.three_smul_kaehlerDifferential_eq_zero hM)

variable (E : Type*) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
  [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E]

/-- The full Jacobian determinant at every integral point of a generating
square presentation is nonzero and has normalized valuation at most the
number of variables. The normalization is `v(3) = 1`. -/
theorem FF.jacobian_det_valuation_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : FF ℤ_[3] ℚ_[3]) (hM : KilledBy 3 M)
    (P : Algebra.Presentation ℤ_[3] M.CoordinateRing ι ι)
    (u : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers E) :
    let d := Matrix.det (fun i j ↦
      aeval (fun k ↦ u (P.val k)) (pderiv j (P.relation i)))
    d ≠ 0 ∧ normalizedIdealOrder E (Ideal.span {d}) ≤ Fintype.card ι := by
  let d := Matrix.det (fun i j ↦
    aeval (fun k ↦ u (P.val k)) (pderiv j (P.relation i)))
  have hdet : u (Matrix.det (fun i j ↦ aeval P.val (pderiv j (P.relation i)))) = d := by
    change u (Matrix.det (Matrix.of (fun i j ↦
      aeval P.val (pderiv j (P.relation i))))) = d
    rw [u.map_det]
    apply congrArg Matrix.det
    apply Matrix.ext
    intro i j
    exact MvPolynomial.comp_aeval_apply P.val u _
  have hd : d ∣ (3 : ThreeAdicIntegers E) ^ Fintype.card ι := by
    have h := map_dvd u (M.jacobian_det_dvd_three_pow hM P)
    simpa only [map_pow, map_ofNat, hdet] using h
  have : CharZero (ThreeAdicIntegers E) := Algebra.charZero_of_charZero ℤ_[3] _
  have hthree : (3 : ThreeAdicIntegers E) ^ Fintype.card ι ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hthree hd
  refine ⟨hd0, ?_⟩
  have hI : Ideal.span {(3 : ThreeAdicIntegers E) ^ Fintype.card ι} ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hthree
  have hle := normalizedIdealOrder_antitone E hI
    (Ideal.span_singleton_le_span_singleton.mpr hd)
  simpa only [← Ideal.span_singleton_pow, normalizedIdealOrder_pow,
    normalizedIdealOrder_three, mul_one] using hle

end ThreeAdicPlan

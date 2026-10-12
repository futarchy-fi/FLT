/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolynomialClosedPointHeight
public import FLT.Mazur.EtaleDimLe

/-!
# Dimension of nonempty etale charts over affine space

Flatness and the heights of closed points give the lower dimension bound;
quasi-finiteness gives the upper bound. This works in every finite dimension.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FCurve
set_option backward.isDefEq.respectTransparency false

variable (K A ι : Type*) [Field K] [CommRing A] [Nontrivial A] [Finite ι]
  [Algebra (MvPolynomial ι K) A]

/-- A nonempty finite type flat chart has dimension at least that of affine space. -/
theorem card_le_ringKrullDim_of_flat_mvPolynomial
    [Algebra.FiniteType (MvPolynomial ι K) A] [Module.Flat (MvPolynomial ι K) A] :
    (Nat.card ι : WithBot ℕ∞) ≤ ringKrullDim A := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  let _ := hM
  let _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing (MvPolynomial ι K) A
  let _ : (M.under (MvPolynomial ι K)).IsMaximal :=
    maximalUnderOfFiniteType (MvPolynomial ι K) A M
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (M.under (MvPolynomial ι K)) M
  have hle : (Nat.card ι : ℕ∞) ≤ M.height := by
    rw [h, mvPolynomial_maximal_height]
    exact le_self_add
  exact (WithBot.coe_le_coe.mpr hle).trans
    (Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top)

/-- Every nonempty etale chart over finite dimensional affine space has that dimension. -/
theorem ringKrullDim_eq_card_of_etale_mvPolynomial [Algebra.Etale (MvPolynomial ι K) A] :
    ringKrullDim A = Nat.card ι := by
  apply le_antisymm _ (card_le_ringKrullDim_of_flat_mvPolynomial K A ι)
  have h := Algebra.QuasiFinite.ringKrullDim_le (MvPolynomial ι K) A
  have hK : ringKrullDim K = 0 :=
    le_antisymm (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 0 K))
      ringKrullDim_nonneg_of_nontrivial
  simpa [hK] using h

end FLT.Mazur.FCurve

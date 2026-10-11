/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationReesCoordinates
public import FLT.Mazur.WeierstrassModificationXResidueConicContraction
public import FLT.Mazur.WeierstrassSuccessiveXConicPuncturedParameters

/-!
# The actual conic punctures on the original horizontal fraction algebra

Transport the original Rees chart through its proved equation equivalence,
then the actual residue conic and its two ordered punctures. The scale and
slope retain their original signs and the original denominator vanishes.
-/

@[expose] public noncomputable section
open IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k < depth) (hπ : π ≠ 0) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "c" => residue R b6
local notation "H" => horizontalReesChart W (π ^ k)
local notation "E" => horizontalReesChartEquiv W (π ^ k) b3 b4 b6 h3 h4 h6 (pow_ne_zero k hπ)
local notation "F" => residueNormalMap D k hk0 (Nat.le_of_lt hk) b3 b4 b6 h3 h4
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D k hk b6 h6)
open WeierstrassSuccessiveX WeierstrassModificationReesCoordinates

/-- The entire original fraction algebra maps to the actual residue conic. -/
def horizontalConicResidue : H →ₐ[R] ConicCoordinate a c :=
  ((fiberConicMap a c).restrictScalars R).comp ((F).comp (E).symm.toAlgHom)

/-- The first original conic puncture, with its positive tangent scale. -/
def horizontalConicFirstResidue : H →ₐ[R] K[T;T⁻¹] :=
  ((conicPuncturedFirst (W.map (residue R)) c hc).restrictScalars R).comp
    (horizontalConicResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6)

/-- The opposite original conic puncture, with its negative tangent scale. -/
def horizontalConicSecondResidue : H →ₐ[R] K[T;T⁻¹] :=
  ((conicPuncturedSecond (W.map (residue R)) c hc).restrictScalars R).comp
    (horizontalConicResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6)

/-- The original scale ratio maps to the original conic incidence coordinate. -/
theorem horizontalConicResidue_scale :
    horizontalConicResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6
      (horizontalScale W (π ^ k)) = conicT a c := by
  rw [← horizontalEquiv_t W (π ^ k) b3 b4 b6 h3 h4 h6 (pow_ne_zero k hπ)]
  simp only [horizontalConicResidue, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply, AlgHom.restrictScalars_apply]
  rw [residueNormalMap_t, fiberConicMap_t]

/-- The original slope ratio maps to the original conic slope coordinate. -/
theorem horizontalConicResidue_slope :
    horizontalConicResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6
      (horizontalVertical W (π ^ k)) = conicV a c := by
  rw [← horizontalEquiv_v W (π ^ k) b3 b4 b6 h3 h4 h6 (pow_ne_zero k hπ)]
  simp only [horizontalConicResidue, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply, AlgHom.restrictScalars_apply]
  rw [residueNormalMap_v, fiberConicMap_v]

/-- On the first puncture the retained scale is a times its Laurent coordinate. -/
theorem horizontalConicFirstResidue_scale :
    horizontalConicFirstResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6
      (horizontalScale W (π ^ k)) = LaurentPolynomial.C a * LaurentPolynomial.T 1 := by
  exact (congrArg (conicPuncturedFirst (W.map (residue R)) c hc)
    (horizontalConicResidue_scale D k hk0 hk hπ b3 b4 b6 h3 h4 h6)).trans
      (conicEvaluation_t ..)

/-- On the opposite puncture the retained scale has the original negative sign. -/
theorem horizontalConicSecondResidue_scale :
    horizontalConicSecondResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6
      (horizontalScale W (π ^ k)) = -LaurentPolynomial.C a * LaurentPolynomial.T 1 := by
  exact (congrArg (conicPuncturedSecond (W.map (residue R)) c hc)
    (horizontalConicResidue_scale D k hk0 hk hπ b3 b4 b6 h3 h4 h6)).trans
      (conicEvaluation_t ..)

/-- The first actual puncture has slope zero. -/
theorem horizontalConicFirstResidue_slope :
    horizontalConicFirstResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6
      (horizontalVertical W (π ^ k)) = 0 := by
  exact (congrArg (conicPuncturedFirst (W.map (residue R)) c hc)
    (horizontalConicResidue_slope D k hk0 hk hπ b3 b4 b6 h3 h4 h6)).trans
      (conicEvaluation_v ..)

/-- The opposite actual puncture has slope minus the original tangent coefficient. -/
theorem horizontalConicSecondResidue_slope :
    horizontalConicSecondResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6
      (horizontalVertical W (π ^ k)) = -LaurentPolynomial.C a := by
  exact (congrArg (conicPuncturedSecond (W.map (residue R)) c hc)
    (horizontalConicResidue_slope D k hk0 hk hπ b3 b4 b6 h3 h4 h6)).trans
      (conicEvaluation_v ..)

omit [IsDomain R] [IsLocalRing R] in
/-- A residue map with invertible scale ratio kills the original horizontal denominator. -/
theorem horizontalResidue_denominator_zero {C : Type u} [CommRing C] [Algebra R C]
    (f : horizontalReesChart W (π ^ k) →ₐ[R] C)
    (hs : algebraMap R C (π ^ k) = 0)
    (hu : IsUnit (f (horizontalScale W (π ^ k)))) :
    f (BlowupFractionChart.denominator
      (WeierstrassDilatation.modificationCenter W (π ^ k))
        (WeierstrassIntegralChart.coord W 2 0)) = 0 := by
  let z : horizontalReesChart W (π ^ k) := BlowupFractionChart.denominator
    (WeierstrassDilatation.modificationCenter W (π ^ k))
    (WeierstrassIntegralChart.coord W 2 0)
  change f z = 0
  apply hu.mul_right_cancel
  rw [zero_mul, ← map_mul]
  have h : z * horizontalScale W (π ^ k) =
      algebraMap R (horizontalReesChart W (π ^ k)) (π ^ k) :=
    BlowupFractionChart.denominator_mul_ratio _ _ _ (Ideal.subset_span (by simp))
  rw [h, f.commutes, hs]

/-- The first puncture kills the original input denominator before localization. -/
theorem horizontalConicFirstResidue_denominator :
    horizontalConicFirstResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6
      (BlowupFractionChart.denominator
        (WeierstrassDilatation.modificationCenter W (π ^ k))
        (WeierstrassIntegralChart.coord W 2 0)) = 0 := by
  apply horizontalResidue_denominator_zero k
  · rw [IsScalarTower.algebraMap_apply R K K[T;T⁻¹], ResidueField.algebraMap_eq,
      WeierstrassDilatation.residue_scale_eq_zero D k hk0, map_zero]
  · rw [horizontalConicFirstResidue_scale]
    exact ((D.a₁_unit.map (residue R)).map LaurentPolynomial.C).mul
      (LaurentPolynomial.isUnit_T 1)

/-- The second puncture kills the original input denominator before localization. -/
theorem horizontalConicSecondResidue_denominator :
    horizontalConicSecondResidue D k hk0 hk hπ b3 b4 b6 h3 h4 h6
      (BlowupFractionChart.denominator
        (WeierstrassDilatation.modificationCenter W (π ^ k))
        (WeierstrassIntegralChart.coord W 2 0)) = 0 := by
  apply horizontalResidue_denominator_zero k
  · rw [IsScalarTower.algebraMap_apply R K K[T;T⁻¹], ResidueField.algebraMap_eq,
      WeierstrassDilatation.residue_scale_eq_zero D k hk0, map_zero]
  · rw [horizontalConicSecondResidue_scale]
    exact ((D.a₁_unit.map (residue R)).map LaurentPolynomial.C).neg.mul
      (LaurentPolynomial.isUnit_T 1)

end FLT.Mazur.WeierstrassModificationX

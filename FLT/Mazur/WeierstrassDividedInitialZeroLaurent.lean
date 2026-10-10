/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialZeroInfinity
public import FLT.Mazur.WeierstrassModificationXZeroResidueLaurent
public import FLT.Mazur.ProjectiveLineSlopeNormalizationCharts

/-!
# The actual start-zero slope chart in the full original Laurent torus

The retained global transition is exactly T=(v+a)/v, with full image D(T-1).
Its normalized projective coordinate is reciprocal to the original T. The
statements concern the existing start-zero open, not hypothetical node sections.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hdepth : 0 < depth) (hstart : start = 0)
  (j : ℕ) (hj : j ≤ n)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "P" => SlopeOpen a
local notation "u" => Units.mk0 a
  (IsUnit.ne_zero (IsUnit.map (residue R) (SplitNodeDepth.a₁_unit D)))
local notation "t" => initialZeroToTensorInfinity hπ data D hdepth hstart j hj
local notation "m" => zeroResidueInfinityTensorMap D hdepth start hstart
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)

/-- The entire start-zero tensor transition preserves its original residue coefficients. -/
@[reassoc] theorem initialZeroToTensorInfinity_structure :
    t ≫ Spec.map (CommRingCat.ofHom
      (algebraMap K (K ⊗[R] WeierstrassIntegralChart.Coordinate W 1))) =
        Spec.map (CommRingCat.ofHom (algebraMap K P)) := by
  rw [← finiteInfinityTensorChart_structure hπ data K j hj,
    initialZeroToTensorInfinity_chart_assoc, initialZeroSlopeChart_structure]

/-- The retained global start-zero transition is the full original tensor algebra map. -/
theorem initialZeroToTensorInfinity_eq_spec :
    t = Spec.map (CommRingCat.ofHom (AlgHom.toRingHom m)) := by
  apply (cancel_mono (pullbackSpecIso R K (WeierstrassIntegralChart.Coordinate W 1)).inv).mp
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSpecIso_inv_fst']
    rw [initialZeroToTensorInfinity_structure, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext (fun r => (AlgHom.commutes m r).symm))
  · simp only [Category.assoc, pullbackSpecIso_inv_snd]
    change t ≫ TensorOpenChart.projection =
      Spec.map (CommRingCat.ofHom (AlgHom.toRingHom m)) ≫ TensorOpenChart.projection
    rw [initialZeroToTensorInfinity_projection, zeroResidueInfinityTensorMap_projection]

/-- The whole actual start-zero transition is the canonical ordered Laurent ratio map. -/
theorem initialZeroToTensorInfinity_laurent :
    t ≫ (infinityResidueIso D hdepth).inv =
      Spec.map (CommRingCat.ofHom (slopeLaurentMap u).toRingHom) := by
  rw [initialZeroToTensorInfinity_eq_spec, ← zeroResidueLaurentMap_spec,
    zeroResidueLaurentMap_eq]

/-- The exact start-zero slope image in original Laurent coordinates is all of D(T-1). -/
theorem initialZeroToTensorInfinity_laurent_range :
    Set.range (t ≫ (infinityResidueIso D hdepth).inv) =
      (PrimeSpectrum.basicOpen (LaurentPolynomial.T 1 - 1 : K[T;T⁻¹]) :
        Set (PrimeSpectrum K[T;T⁻¹])) := by
  rw [initialZeroToTensorInfinity_laurent]
  exact slopeLaurentMap_range u

/-- The full original Laurent chart embeds into the retained model at start zero. -/
def initialZeroLaurentChart : ProjectiveLine.overlap K ⟶
    finiteGlobalTensorModel hπ data K j hj :=
  (infinityResidueIso D hdepth).hom ≫ finiteInfinityTensorChart hπ data K j hj

instance initialZeroLaurentChart_isOpenImmersion :
    IsOpenImmersion (initialZeroLaurentChart hπ data D hdepth j hj) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The complete original slope chart factors through the actual entire Laurent open. -/
@[reassoc] theorem initialZeroSlopeChart_laurent :
    Spec.map (CommRingCat.ofHom (slopeLaurentMap u).toRingHom) ≫
      initialZeroLaurentChart hπ data D hdepth j hj =
        initialZeroSlopeChart hπ data D hdepth hstart j hj := by
  rw [← initialZeroToTensorInfinity_laurent hπ data D hdepth hstart j hj,
    initialZeroLaurentChart, Category.assoc, Iso.inv_hom_id_assoc,
    initialZeroToTensorInfinity_chart]

/-- The actual Laurent open retains the original coefficient projection. -/
@[reassoc] theorem initialZeroLaurentChart_structure :
    initialZeroLaurentChart hπ data D hdepth j hj ≫ pullback.fst _ _ =
      (MultiplicativeGroupScheme.gm K).hom := by
  rw [initialZeroLaurentChart, Category.assoc, finiteInfinityTensorChart_structure,
    infinityResidueIso_structure]

/-- Start-zero slope coordinates normalize with the same reciprocal original Laurent parameter. -/
@[reassoc] theorem initialZeroSlope_normalized :
    PrincipalOpenTransport.inclusion (slopePolynomial a) ≫ ProjectiveLine.left K ≫
        (ProjectiveLine.slopeNormalizationIso u).hom =
      (t ≫ (infinityResidueIso D hdepth).inv) ≫
        ProjectiveLine.overlapRight K ≫ ProjectiveLine.left K := by
  rw [initialZeroToTensorInfinity_laurent]
  have h := congrArg (· ≫ (ProjectiveLine.slopeNormalizationIso u).hom)
    (ProjectiveLine.infinityTorus_slope_condition u)
  simp only [Category.assoc, ProjectiveLine.slopeNormalization_infinityTorus_left] at h
  exact h

end FLT.Mazur.WeierstrassDividedDepth

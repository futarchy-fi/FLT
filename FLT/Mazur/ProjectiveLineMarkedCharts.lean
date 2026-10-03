/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonDivisorNormalizationPullback

/-!
# Affine charts of the actual marked-point ideal

The marked section has coordinates a and a⁻¹ in the two polynomial charts.
Pulling its ideal to either chart gives the corresponding evaluation kernel,
whose equation is X minus that coordinate.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.ProjectiveLineMarkedCharts
open PolygonDivisorNormalizationPullback ProjectiveLineActionSpecialization
variable (K : Type u) [Field K]

/-- The point of the polynomial chart with the specified coordinate. -/
def chartPoint (a : K) : Spec (.of K) ⟶ ProjectiveLine.chart K :=
  Spec.map (CommRingCat.ofHom (evalRingHom a))

/-- The unit parameter is the left affine coordinate. -/
theorem unitPoint_overlapLeft (a : Kˣ) :
    unitPoint K a ≫ ProjectiveLine.overlapLeft K = chartPoint K a := by
  rw [unitPoint, ProjectiveLine.overlapLeft, chartPoint, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · simp

/-- Inversion sends a unit-marked point to the reciprocal unit. -/
theorem unitPoint_inversion (a : Kˣ) :
    unitPoint K a ≫ (ProjectiveLine.inversion K).hom = unitPoint K a⁻¹ := by
  rw [unitPoint, ProjectiveLine.inversion_hom, ← Spec.map_comp, unitPoint]
  congr 1
  apply CommRingCat.hom_ext
  apply PolygonScalingNaturality.ringHom_ext
  · intro r
    simp
  · simp
  · simp

/-- The left-chart marked point is the specified normalization section. -/
theorem left_point (a : Kˣ) :
    chartPoint K a ≫ ProjectiveLine.left K = markedPoint K a := by
  rw [← unitPoint_overlapLeft]
  rfl

/-- The right-chart coordinate of that same point is the reciprocal unit. -/
theorem right_point (a : Kˣ) :
    chartPoint K (a⁻¹ : Kˣ) ≫ ProjectiveLine.right K = markedPoint K a := by
  rw [markedPoint]
  change _ = unitPoint K a ≫ ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K
  rw [ProjectiveLine.overlap_condition, ProjectiveLine.overlapRight,
    ← Category.assoc, ← Category.assoc, unitPoint_inversion, unitPoint_overlapLeft]

/-- The marked point is a section of P1 over its coefficient field. -/
theorem point_base (a : Kˣ) : markedPoint K a ≫ ProjectiveLine.toBase K = 𝟙 _ := by
  rw [← left_point, Category.assoc, ProjectiveLine.left_toBase]
  rw [chartPoint, ProjectiveLine.chartToBase, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext r
  simp

instance point_closed (a : Kˣ) : IsClosedImmersion (markedPoint K a) := by
  let := PolygonProper.projectiveLine K
  exact FCurve.isClosedImmersion_section _ _ (point_base K a)

/-- Pulling a closed composite back along a monomorphism recovers its kernel. -/
theorem ker_comap_mono {X Y Z : Scheme.{u}} (s : Z ⟶ X) (j : X ⟶ Y)
    [Mono j] [IsClosedImmersion (s ≫ j)] : (s ≫ j).ker.comap j = s.ker := by
  have H : IsPullback s (𝟙 _) j (s ≫ j) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom, H.isoPullback_hom_fst]

/-- The actual marked ideal on the left chart is the evaluation kernel. -/
theorem left_ideal (a : Kˣ) :
    (markedPoint K a).ker.comap (ProjectiveLine.left K) = (chartPoint K a).ker := by
  have : IsClosedImmersion (chartPoint K a ≫ ProjectiveLine.left K) :=
    (left_point K a).symm ▸ inferInstance
  rw [← left_point, ker_comap_mono]

/-- The right chart carries the reciprocal-coordinate evaluation kernel. -/
theorem right_ideal (a : Kˣ) :
    (markedPoint K a).ker.comap (ProjectiveLine.right K) =
      (chartPoint K (a⁻¹ : Kˣ)).ker := by
  have : IsClosedImmersion (chartPoint K (a⁻¹ : Kˣ) ≫ ProjectiveLine.right K) :=
    (right_point K a).symm ▸ inferInstance
  rw [← right_point, ker_comap_mono]
/-- The polynomial coordinate equation of the actual affine section ideal. -/
theorem chart_ideal (a : K) :
    ((chartPoint K a).ker.ideal ⟨⊤, isAffineOpen_top _⟩).comap
      (Scheme.ΓSpecIso (.of K[X])).inv.hom = Ideal.span {X - C a} := by
  rw [Scheme.ker_of_isAffine]
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal]
  simp only [homOfLE_refl, op_id]
  rw [CategoryTheory.Functor.map_id]
  simp only [CommRingCat.hom_id, Ideal.map_id]
  rw [← ker_evalRingHom]
  ext f
  change (chartPoint K a).appTop.hom ((Scheme.ΓSpecIso (.of K[X])).inv.hom f) = 0 ↔
    eval a f = 0
  have he := congrArg (fun k ↦ k.hom f)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (evalRingHom a)))
  change (Scheme.ΓSpecIso (.of K)).inv.hom (eval a f) =
    (chartPoint K a).appTop.hom ((Scheme.ΓSpecIso (.of K[X])).inv.hom f) at he
  rw [← he]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of K)).inv).injective
/-- The marked P1 section is a relative effective Cartier divisor. -/
theorem relativeCartier (a : Kˣ) :
    FCurve.RelativeEffectiveCartier (ProjectiveLine.toBase K) (markedPoint K a).ker := by
  let j := (PolygonPinching.torusToComponent K).left
  let := PolygonProper.projectiveLine K
  have hd : SmoothOfRelativeDimension 1 (j ≫ ProjectiveLine.toBase K) := by
    change SmoothOfRelativeDimension 1
      ((PolygonPinching.torusToComponent K).left ≫ (PolygonPinching.component K).hom)
    rw [Over.w]
    exact MultiplicativeGroupDimension.dimension K
  exact FCurve.smoothOpenSectionCartier j (ProjectiveLine.toBase K) (unitPoint K a)
    inferInstance hd inferInstance (by simpa [markedPoint, Category.assoc] using point_base K a)
end FLT.Mazur.ProjectiveLineMarkedCharts

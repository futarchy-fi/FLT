/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroInfinityBoundary
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroInitialProjection
public import FLT.Mazur.WeierstrassResidueInfinitySlopeComparison
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroInitialProjection
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroInfinityBoundary
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorCoconeMaps

/-!
# The original infinity parameter on the entire start-zero boundary

Both actual projections determine the original parameter on the whole shifted
vertical open. The first retained conic constant remains unrestricted.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
set_option maxRecDepth 2048
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "e" => data ⟨1, by omega⟩
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hr" => residueTangentEquation_root W
local notation "hscale" => show algebraMap R Q (π ^ 0) = 1 from by simp
local notation "gc" => coefficientShearResidueZeroInitial_coefficients hπ hm data s hs
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "a" => (U).a₁
local notation "P" => SlopeOpen a
local notation "z" => (slopeZ a * (slopeZ a + algebraMap Q P a)) *
  (slopeZ a + algebraMap Q P r)
local notation "y" => WeierstrassModificationX.y W (π ^ 0) (d).b3 (d).b4 (d).b6
local notation "ci" => incidenceCoefficientShearIso W (π ^ 0) (d).b3 (d).b4 (d).b6 Q r
local notation "I" => coefficientShearResidueZeroInitialIso hπ hm data s hs
local notation "e₀" => tensorShearScaleOneEquiv W (π ^ 0) (d).b3 (d).b4 (d).b6
  Q r hscale (gc).1 (gc).2.1 (gc).2.2 hr
local notation "N" => Scheme.Spec.mapIso (e₀).toRingEquiv.toCommRingCatIso.op
local notation "L" => tensorShearScaleOneInfinityIso W (π ^ 0) (d).b3 (d).b4 (d).b6
  Q r hscale (gc).1 (gc).2.1 (gc).2.2 hr
local notation "p" => PrincipalOpenTransport.inclusion z

variable [IsBezout R]
variable (h3 : algebraMap R (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (data ⟨1, by omega⟩).b3 = 0)
  (h4 : algebraMap R (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (data ⟨1, by omega⟩).b4 = 0)
local notation "b" => coefficientShearResidueZeroInfinityBoundary hπ hm data s hs
local notation "c" => coefficientShearGluedChart hπ data Q r (s + 1) hs
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap (Polynomial Q) P))

/-- The full shifted boundary has its original initial projection in the glued model. -/
theorem coefficientShearResidueZeroInfinityBoundary_glued :
    b ≫ c (.inl 0) = p ≫ (I).hom ≫ c (.inl 2) := by
  apply (cancel_mono (coefficientShearGluedIso hπ data Q r (s + 1) hs).hom).mp
  simp only [Category.assoc, coefficientShearGluedIso_chart]
  exact coefficientShearResidueZeroInfinityBoundary_comp hπ hm data s hs

/-- The entire original infinity boundary keeps its coefficient structure. -/
@[reassoc] theorem coefficientShearResidueZeroInfinityBoundary_structure :
    b ≫ coefficientShearAtlasStructure data Q r (s + 1) hs (.inl 0) =
      p ≫ q ≫ ProjectiveLine.left Q ≫ ProjectiveLine.toBase Q := by
  have H := congrArg (· ≫ coefficientShearGluedStructure hπ data Q r (s + 1) hs)
    (coefficientShearResidueZeroInfinityBoundary_glued hπ hm data s hs)
  simp only [Category.assoc, coefficientShearGluedChart_structure] at H
  rw [H, ProjectiveLine.left_toBase]
  congr 1
  change (I).hom ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  exact terminalComponent_algebra_structure
    (coefficientShearScaleOneEquiv W (π ^ 0) (d).b3 (d).b4 (d).b6
      Q r hscale (gc).1 (gc).2.1 (gc).2.2 hr).toAlgHom

include h3 h4 in
/-- Every original cubic function agrees with the complete original normalization. -/
theorem coefficientShearResidueZeroInfinityBoundary_toCurve :
    b ≫ TensorOpenChart.projection ≫ WeierstrassIntegralChart.integralCurveChart W 1 =
      p ≫ q ≫ ProjectiveLine.left Q ≫ originalResidueCompleteNormalization
        e (by simp) (nodalDepth_residue_uniformizer hm) := by
  have H := congrArg (· ≫ coefficientShearGluedProjection hπ data Q r (s + 1) hs ≫
      finiteGlobalContraction hπ data (s + 1) hs)
    (coefficientShearResidueZeroInfinityBoundary_glued hπ hm data s hs)
  simp only [Category.assoc] at H
  rw [coefficientShearGluedChart_projection_assoc] at H
  change b ≫ finiteInfinityTensorChart hπ data Q (s + 1) hs ≫ _ ≫ _ = _ at H
  rw [finiteInfinityTensorChart_toCurve] at H
  rw [← coefficientShearResidueZeroInitialIso_toCurve hπ hm data s hs h3 h4]
  exact H

variable (u : (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))ˣ)
  (hu : (u : AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) =
    (nodeTangentShear (W.map (residue R))).a₁)

include h3 h4 in
/-- The full original shifted boundary has exactly its original slope parameter. -/
theorem coefficientShearResidueZeroInfinityBoundary_parameter :
    b ≫ residueInfinityTensorParameter e (by simp)
      (nodalDepth_residue_uniformizer hm) u hu = p ≫ q ≫ ProjectiveLine.left Q := by
  have H := residueInfinityTensorParameter_slope e (by simp)
    (nodalDepth_residue_uniformizer hm) u hu (X := Spec (.of (Localization.Away z)))
  have hu' : (u : Q) = a := hu
  rw [hu'] at H
  apply H p b
  · exact coefficientShearResidueZeroInfinityBoundary_structure hπ hm data s hs
  · exact coefficientShearResidueZeroInfinityBoundary_toCurve hπ hm data s hs h3 h4

end FLT.Mazur.WeierstrassDividedDepth

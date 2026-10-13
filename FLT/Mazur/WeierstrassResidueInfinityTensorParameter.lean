/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentNormalizationInfinity
public import FLT.Mazur.WeierstrassDividedCompleteResidueNormalization
public import FLT.Mazur.WeierstrassChartBaseChange
public import FLT.Mazur.TensorOpenChart

/-!
# The original infinity tensor chart factors through the complete residue normalization

The explicit coefficient comparison keeps the whole original tensor algebra.
Its infinity parameter reconstructs the original integral cubic chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (d : Data W π k) (hk : 0 < k) (hπ : residue R π = 0)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "U" => (V).map (algebraMap (ResidueField R) Q)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "h" => originalResidue_normalization_coefficients d hk hπ

/-- The original tensor infinity chart is the full coefficient-extended cubic chart. -/
def residueInfinityTensorIso : chartScheme U 1 ≅ Spec (.of (Q ⊗[R] Coordinate W 1)) :=
  Scheme.Spec.mapIso (chartBaseChangeEquiv Q W 1).toRingEquiv.toCommRingCatIso.op

/-- The tensor comparison retains the actual coefficient structure. -/
@[reassoc] theorem residueInfinityTensorIso_structure :
    (residueInfinityTensorIso (W := W)).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap Q (Q ⊗[R] Coordinate W 1))) =
        chartStructure U 1 := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (chartBaseChangeEquiv Q W 1).commutes)

/-- Its integral projection is the composite of the two original coefficient chart maps. -/
@[reassoc] theorem residueInfinityTensorIso_projection :
    (residueInfinityTensorIso (W := W)).hom ≫ TensorOpenChart.projection =
      chartCoefficientMorphism V 1 ≫ chartCoefficientMorphism W 1 := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  change (((chartBaseChangeEquiv Q W 1).toAlgHom.restrictScalars R).comp
    Algebra.TensorProduct.includeRight).toRingHom =
      (((chartCoefficientMap V 1).restrictScalars R).comp (chartCoefficientMap W 1)).toRingHom
  congr 1
  apply hom_ext
  intro i
  change chartBaseChangeEquiv Q W 1 ((1 : Q) ⊗ₜ[R] coord W 1 i) =
    chartCoefficientMap V 1 (chartCoefficientMap W 1 (coord W 1 i))
  rw [chartBaseChangeEquiv_coord, chartCoefficientMap_coord]
  exact (chartCoefficientMap_coord V 1 i).symm

variable (a : (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))ˣ)
  (ha : (a : AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) =
    (nodeTangentShear (W.map (residue R))).a₁)

/-- The entire original infinity tensor chart has a parameter on the complete exterior. -/
def residueInfinityTensorParameter : Spec (.of (Q ⊗[R] Coordinate W 1)) ⟶ scheme Q :=
  (residueInfinityTensorIso (W := W)).inv ≫
    nodeTangentInfinityParameter V (h).1 (h).2.1 (h).2.2 a ha

/-- The full parameter preserves its original residue-root structure. -/
@[reassoc] theorem residueInfinityTensorParameter_structure :
    residueInfinityTensorParameter d hk hπ a ha ≫ toBase Q =
      Spec.map (CommRingCat.ofHom (algebraMap Q (Q ⊗[R] Coordinate W 1))) := by
  rw [residueInfinityTensorParameter, Category.assoc,
    nodeTangentInfinityParameter_structure, ← residueInfinityTensorIso_structure,
    Iso.inv_hom_id_assoc]

/-- Every original cubic function is retained, including at infinity. -/
@[reassoc] theorem residueInfinityTensorParameter_normalization :
    residueInfinityTensorParameter d hk hπ a ha ≫
      originalResidueCompleteNormalization d hk hπ =
        TensorOpenChart.projection ≫ integralCurveChart W 1 := by
  apply (cancel_epi (residueInfinityTensorIso (W := W)).hom).mp
  rw [residueInfinityTensorParameter, Category.assoc, Iso.hom_inv_id_assoc,
    originalResidueCompleteNormalization, nodeTangentInfinityParameter_normalization_assoc]
  erw [integralCurveChart_coefficientMorphism]
  rw [residueInfinityTensorIso_projection_assoc]

end FLT.Mazur.WeierstrassDividedDepth

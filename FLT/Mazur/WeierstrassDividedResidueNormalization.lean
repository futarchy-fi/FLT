/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentCoefficientNaturality
public import FLT.Mazur.NodeTangentProjectiveLineDescent
public import FLT.Mazur.WeierstrassChartCoefficientMap
public import FLT.Mazur.WeierstrassDividedDepthData

/-!
# Normalization of the original divided model's residue equation

Positive divided-depth data forces the three actual original residue
coefficients to vanish. The root normalization therefore maps to that
original integral cubic chart; conjugation fixes its entire projection.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (d : Data W π k) (hk : 0 < k) (hπ : residue R π = 0)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)

include d hk hπ in
/-- The original divided-depth factorizations force the actual residue cubic to be nodal in form. -/
theorem originalResidue_normalization_coefficients : (V).a₃ = 0 ∧ (V).a₄ = 0 ∧ (V).a₆ = 0 := by
  change residue R W.a₃ = 0 ∧ residue R W.a₄ = 0 ∧ residue R W.a₆ = 0
  rw [d.factor3, d.factor4, d.factor6]
  simp [hπ, ne_of_gt hk]

/-- Normalize the residue equation while retaining the original integral affine chart projection. -/
def originalResidueNormalization : Coordinate W 2 →+* Polynomial Q :=
  (nodeTangentNormalizationChart V
    (originalResidue_normalization_coefficients d hk hπ).1
    (originalResidue_normalization_coefficients d hk hπ).2.1
    (originalResidue_normalization_coefficients d hk hπ).2.2).toRingHom.comp
      (chartCoefficientMap (S := ResidueField R) W 2).toRingHom

/-- Both original affine coordinates retain their actual root-sheared residue values. -/
@[simp] theorem originalResidueNormalization_coord (i : Fin 3) :
    originalResidueNormalization d hk hπ (coord W 2 i) =
      ![nodeTangentNormalizationX V, nodeTangentNormalizationY V, 1] i := by
  change nodeTangentNormalizationChart V
    (originalResidue_normalization_coefficients d hk hπ).1
    (originalResidue_normalization_coefficients d hk hπ).2.1
    (originalResidue_normalization_coefficients d hk hπ).2.2
    (chartCoefficientMap (S := ResidueField R) W 2 (coord W 2 i)) = _
  rw [chartCoefficientMap_coord]
  exact nodeTangentNormalizationChart_coord V _ _ _ i

/-- Every original integral chart function is fixed after residue normalization. -/
theorem originalResidueNormalization_conjugation :
    (nodeTangentNormalizationConjugation V).toRingHom.comp
        (originalResidueNormalization d hk hπ) = originalResidueNormalization d hk hπ := by
  have h := congrArg AlgHom.toRingHom
    (nodeTangentNormalizationConjugation_chart V
      (originalResidue_normalization_coefficients d hk hπ).1
      (originalResidue_normalization_coefficients d hk hπ).2.1
      (originalResidue_normalization_coefficients d hk hπ).2.2)
  exact congrArg (fun g => g.comp (chartCoefficientMap (S := ResidueField R) W 2).toRingHom) h

/-- The residue normalization map to the original integral cubic chart. -/
def originalResidueNormalizationMap :
    Spec (.of (Polynomial Q)) ⟶ Spec (.of (Coordinate W 2)) :=
  Spec.map (CommRingCat.ofHom (originalResidueNormalization d hk hπ))

/-- Actual residue conjugation preserves the original chart projection as a scheme morphism. -/
@[reassoc] theorem originalResidueNormalizationMap_conjugation :
    Spec.map (CommRingCat.ofHom (nodeTangentNormalizationConjugation V).toRingHom) ≫
        originalResidueNormalizationMap d hk hπ = originalResidueNormalizationMap d hk hπ := by
  simpa only [originalResidueNormalizationMap, CommRingCat.ofHom_comp, Spec.map_comp] using
    congrArg (fun g => Spec.map (CommRingCat.ofHom g))
      (originalResidueNormalization_conjugation d hk hπ)

/-- The retained map to the original projective cubic is also fixed by the same operation. -/
@[reassoc] theorem originalResidueNormalizationMap_toCurve :
    Spec.map (CommRingCat.ofHom (nodeTangentNormalizationConjugation V).toRingHom) ≫
        originalResidueNormalizationMap d hk hπ ≫ integralCurveChart W 2 =
      originalResidueNormalizationMap d hk hπ ≫ integralCurveChart W 2 := by
  rw [originalResidueNormalizationMap_conjugation_assoc]

end FLT.Mazur.WeierstrassDividedDepth

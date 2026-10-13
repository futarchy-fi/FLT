/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassResidueInfinityTensorParameter
public import FLT.Mazur.NodeTangentInfinitySlopeCompatibility
public import FLT.Mazur.WeierstrassIntegralBaseChange
import all FLT.Mazur.NodeTangentNormalizationInfinity

/-!
# Recovering the infinity slope with its actual coefficient projection

The two coefficient pullbacks recover the root-extended cubic from its original
integral projection and its coefficient structure. Neither projection is canceled.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart ProjectiveLine WeierstrassModificationX
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
  (a : (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))ˣ)
  (ha : (a : AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) =
    (nodeTangentShear (W.map (residue R))).a₁)
local notation "h" => originalResidue_normalization_coefficients d hk hπ
local notation "b" => nodeTangentShear_normalization_coefficients V (h).1 (h).2.1 (h).2.2
local notation "N" => splitCompleteNormalization (nodeTangentShear V)
  (b).1 (b).2.1 (b).2.2.1 (b).2.2.2
local notation "i" => integralVariableChangeIso U (nodeTangentShear V)
  (WeierstrassCurve.VariableChange.mk 1 0 (AdjoinRoot.root (nodeTangentPolynomial V)) 0) rfl
local notation "s" => PrincipalOpenTransport.inclusion (slopePolynomial (a : Q))
local notation "P" => residueInfinityTensorParameter d hk hπ a ha

/-- Original cubic functions and coefficient structure determine the full infinity slope. -/
theorem residueInfinityTensorParameter_slope {X : Scheme}
    (f : X ⟶ Spec (.of (SlopeOpen (a : Q))))
    (g : X ⟶ Spec (.of (Q ⊗[R] Coordinate W 1)))
    (hbase : g ≫ Spec.map (CommRingCat.ofHom (algebraMap Q (Q ⊗[R] Coordinate W 1))) =
      f ≫ s ≫ left Q ≫ toBase Q)
    (hcurve : g ≫ TensorOpenChart.projection ≫ integralCurveChart W 1 =
      f ≫ s ≫ left Q ≫ originalResidueCompleteNormalization d hk hπ) :
    g ≫ P = f ≫ s ≫ left Q := by
  let t := g ≫ (residueInfinityTensorIso (W := W)).inv
  have ht : t ≫ chartStructure U 1 = f ≫ s ≫ left Q ≫ toBase Q := by
    change (g ≫ (residueInfinityTensorIso (W := W)).inv) ≫ _ = _
    rw [Category.assoc, ← residueInfinityTensorIso_structure (W := W),
      Iso.inv_hom_id_assoc]
    exact hbase
  rw [residueInfinityTensorParameter, ← Category.assoc]
  change t ≫ nodeTangentInfinityParameter V (h).1 (h).2.1 (h).2.2 a ha = _
  apply nodeTangentInfinityParameter_slope V (h).1 (h).2.1 (h).2.2 a ha f t
  have H := (integralCoefficient_isPullback (S := Q) V).paste_horiz
    (integralCoefficient_isPullback (S := ResidueField R) W)
  apply H.hom_ext
  · have hn : N ≫ (i).hom ≫ integralCoefficientMorphism (S := Q) V ≫
        integralCoefficientMorphism (S := ResidueField R) W =
        originalResidueCompleteNormalization d hk hπ := by
      rw [originalResidueCompleteNormalization, nodeTangentCompleteNormalization_eq_split]
      simp only [Category.assoc]
    simp only [Category.assoc]
    rw [← nodeTangentInfinityParameter_split V (h).1 (h).2.1 (h).2.2 a ha]
    simp only [Category.assoc]
    rw [hn]
    have hp := residueInfinityTensorParameter_normalization d hk hπ a ha
    simp only [residueInfinityTensorParameter, Category.assoc] at hp
    change (g ≫ (residueInfinityTensorIso (W := W)).inv) ≫ _ = _
    rw [Category.assoc, hp, hcurve]
  · simp only [Category.assoc, integralCurveChart_structure]
    have hi : (i).hom ≫ integralCurveStructure U =
        integralCurveStructure (nodeTangentShear V) :=
      integralVariableChangeTo_structure U (nodeTangentShear V)
        (WeierstrassCurve.VariableChange.mk 1 0
          (AdjoinRoot.root (nodeTangentPolynomial V)) 0) rfl
    rw [hi, splitCompleteNormalization_base, ht]

end FLT.Mazur.WeierstrassDividedDepth

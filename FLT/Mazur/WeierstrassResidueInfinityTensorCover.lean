/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentInfinityParameterCover
public import FLT.Mazur.WeierstrassResidueInfinityTensorParameter
public import FLT.Mazur.WeierstrassDividedCompleteResidueNormalization
public import FLT.Mazur.WeierstrassChartBaseChange
public import FLT.Mazur.TensorOpenChart

/-!
# The full original tensor infinity chart detects exterior morphisms

Transport the actual shifted open cover along the original coefficient comparison.
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

variable (a : (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))ˣ)
  (ha : (a : AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) =
    (nodeTangentShear (W.map (residue R))).a₁)

local notation "P" => residueInfinityTensorParameter d hk hπ a ha

/-- The original tensor infinity parameter is an open immersion. -/
instance residueInfinityTensorParameter_isOpenImmersion : IsOpenImmersion P := by
  unfold residueInfinityTensorParameter
  infer_instance

/-- The entire tensor infinity chart and full affine line cover the original normalization. -/
theorem residueInfinityTensorParameter_cover (x : scheme Q) :
    x ∈ Set.range (left Q) ∨ x ∈ Set.range P := by
  rcases nodeTangentInfinityParameter_cover V (h).1 (h).2.1 (h).2.2 a ha x with hl | hi
  · exact Or.inl hl
  · obtain ⟨y, rfl⟩ := hi
    right
    refine ⟨(residueInfinityTensorIso (W := W)).hom y, ?_⟩
    change ((residueInfinityTensorIso (W := W)).hom ≫ P) y = _
    rw [residueInfinityTensorParameter, Iso.hom_inv_id_assoc]

/-- Full original source charts detect morphisms to arbitrary targets. -/
theorem residueInfinityTensorParameter_hom_ext {Y : Scheme} (f g : scheme Q ⟶ Y)
    (hl : left Q ≫ f = left Q ≫ g) (hi : P ≫ f = P ≫ g) : f = g :=
  BinaryOpenDescent.hom_ext (left Q) P
    (residueInfinityTensorParameter_cover d hk hπ a ha) f g hl hi

end FLT.Mazur.WeierstrassDividedDepth

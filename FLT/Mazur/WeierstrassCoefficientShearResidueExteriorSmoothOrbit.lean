/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueExteriorLift
public import FLT.Mazur.WeierstrassCoefficientShearSmoothOrbitRecovery
public import FLT.Mazur.WeierstrassResidueTangentCoefficientTower
public import FLT.Mazur.NodeTangentSmoothNormalization

/-!
# The complete punctured residue exterior is the retained original smooth orbit

The actual ordered exterior, including its Laurent orientation, agrees with
the independently constructed original smooth embedding. Its full range is
therefore the original smooth orbit, without discarding any scheme points.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  {k : ℕ} (d : Data W π k) (hk : 0 < k) (hres : residue R π = 0)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "U" => (V).map (algebraMap (ResidueField R) Q)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
  (a : (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))ˣ)
  (ha : (a : AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) =
    (nodeTangentShear (W.map (residue R))).a₁)
local notation "h" => originalResidue_normalization_coefficients d hk hres
local notation "h3" => show (U).a₃ = 0 from by
  exact (congrArg (algebraMap (ResidueField R) Q) (h).1).trans (map_zero _)
local notation "h4" => show (U).a₄ = 0 from by
  exact (congrArg (algebraMap (ResidueField R) Q) (h).2.1).trans (map_zero _)
local notation "h6" => show (U).a₆ = 0 from by
  exact (congrArg (algebraMap (ResidueField R) Q) (h).2.2).trans (map_zero _)
local notation "I" => rootShearTorusSmoothIso U r a
  (ha.trans (nodeTangentShear_coefficients V).1) (nodeTangentRoot_equation V) h3 h4 h6
local notation "F" => coefficientShearResidueExteriorLift hπ data j hj d hk hres a
local notation "B" => coefficientShearSmoothEmbedding hπ data Q r j hj
local notation "t" => (PolygonPinching.torusToComponent Q).left

/-- The full punctured exterior has exactly the independently constructed smooth-orbit map. -/
@[reassoc] theorem coefficientShearResidueExteriorLift_smoothOrbit :
    (inversion Q).hom ≫ t ≫ F = (I).hom ≫ B := by
  apply coefficientShearSmoothEmbedding_recover
  · change ((inversion Q).hom ≫ t ≫ F) ≫
      coefficientShearGluedStructure hπ data Q r j hj =
        (I).hom ≫ integralSmoothStructure U
    simp only [Category.assoc]
    rw [coefficientShearResidueExteriorLift_structure hπ data j hj d hk hres a]
    rw [rootShearTorusSmoothIso_structure]
    change (inversion Q).hom ≫ overlapLeft Q ≫ left Q ≫ toBase Q = _
    rw [left_toBase, OneGonNormalization.overlapLeft_toBase]
    exact OneGonNormalization.inversion_toBase Q
  · simp only [Category.assoc]
    rw [coefficientShearResidueExteriorLift_toCurve,
      ← originalResidueCompleteNormalization_eq_splitCubic,
      originalResidueCompleteNormalization]
    erw [nodeTangentNormalization_orderedTorus_smooth_assoc V (h).1 (h).2.1 (h).2.2 a ha]
    rw [residueTangentIntegralCoefficient_comp]
    rfl

include ha in
/-- The entire punctured original exterior equals the full retained smooth orbit as a set. -/
theorem coefficientShearResidueExteriorLift_smoothOrbit_range :
    Set.range (t ≫ F) = Set.range B := by
  have hmap := coefficientShearResidueExteriorLift_smoothOrbit hπ data j hj d hk hres a ha
  have hr := congrArg (fun f : (MultiplicativeGroupScheme.gm Q).left ⟶
    coefficientShearGlued hπ data Q r j hj => Set.range f) hmap
  have hi : Function.Surjective ((inversion Q).hom : _ → _) :=
    (inversion Q).hom.homeomorph.surjective
  have hj : Function.Surjective ((I).hom : _ → _) := (I).hom.homeomorph.surjective
  change Set.range ((t ≫ F) ∘ (inversion Q).hom) = Set.range (B ∘ (I).hom) at hr
  rw [hi.range_comp, hj.range_comp] at hr
  exact hr

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueOrderedExterior
public import FLT.Mazur.WeierstrassResidueTangentComponentData

/-!
# The ordered exterior in the actual residue-tangent target

Lift the complete original ordered normalization through the actual coefficient
pullback. Its whole integral specialization and full semilinear reflection are
retained, together with the complete original cubic contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  {k : ℕ} (d : Data W π k) (hk : 0 < k) (hres : residue R π = 0)
local notation "V" => W.map (residue R)
local notation "A" => AdjoinRoot (nodeTangentPolynomial W)
local notation "rA" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
  (a : (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))ˣ)
local notation "sQ" => coefficientShearGluedStructure hπ data Q r j hj
local notation "pQ" => coefficientShearGluedProjection hπ data Q r j hj
local notation "pA" => coefficientShearGluedProjection hπ data A rA j hj
local notation "sA" => coefficientShearGluedStructure hπ data A rA j hj
local notation "M" => coefficientShearTangentSpecialization hπ data j hj
local notation "F" => coefficientShearResidueOrderedExterior hπ data j hj d hk hres a
/-- Seal the complete ordered finite normalization before using its coefficient pullback. -/
@[irreducible] def coefficientShearResidueOrderedFinite :
    scheme Q ⟶ finiteGlobalModel hπ data j hj :=
  (slopeNormalizationIso a).inv ≫ originalResidueFiniteNormalization hπ data j hj d hk hres
local notation "N" => coefficientShearResidueOrderedFinite hπ data j hj d hk hres a

/-- The entire ordered finite normalization lies over the actual residue coefficient map. -/
theorem coefficientShearResidueExteriorLift_square :
    toBase Q ≫ Spec.map (CommRingCat.ofHom (algebraMap R Q)) =
      N ≫ finiteGlobalStructure hπ data j hj := by
  rw [coefficientShearResidueOrderedFinite, Category.assoc,
    originalResidueFiniteNormalization_base,
    slopeNormalizationIso_inv_base_assoc]
  rfl

/-- The full ordered exterior in the actual residue-root coefficient model. -/
@[irreducible] def coefficientShearResidueExteriorLift :
    scheme Q ⟶ coefficientShearGlued hπ data Q r j hj :=
  (coefficientShearGlued_isPullback hπ data Q r j hj).lift (toBase Q) N
    (coefficientShearResidueExteriorLift_square hπ data j hj d hk hres a)
local notation "L" => coefficientShearResidueExteriorLift hπ data j hj d hk hres a

/-- Its coefficient structure is the original residue field, on the complete component. -/
@[reassoc] theorem coefficientShearResidueExteriorLift_structure : L ≫ sQ = toBase Q := by
  rw [coefficientShearResidueExteriorLift]
  exact (coefficientShearGlued_isPullback hπ data Q r j hj).lift_fst _ _ _

/-- Its full finite-model projection retains the original ordered normalization. -/
@[reassoc] theorem coefficientShearResidueExteriorLift_projection : L ≫ pQ = N := by
  rw [coefficientShearResidueExteriorLift]
  exact (coefficientShearGlued_isPullback hπ data Q r j hj).lift_snd _ _ _

/-- Actual coefficient specialization recovers the complete integral-target ordered exterior. -/
@[reassoc] theorem coefficientShearResidueExteriorLift_specialization : L ≫ M = F := by
  apply (coefficientShearGlued_isPullback hπ data A rA j hj).hom_ext
  · rw [Category.assoc, coefficientShearTangentSpecialization,
      coefficientShearSpecialization_structure,
      coefficientShearResidueExteriorLift_structure_assoc,
      coefficientShearResidueOrderedExterior, Category.assoc,
      coefficientShearResidueExterior_structure, slopeNormalizationIso_inv_base_assoc]
    rfl
  · rw [Category.assoc, coefficientShearTangentSpecialization,
      coefficientShearSpecialization_projection, coefficientShearResidueExteriorLift_projection,
      coefficientShearResidueOrderedFinite, coefficientShearResidueOrderedExterior,
      Category.assoc,
      coefficientShearResidueExterior_projection]

/-- The complete lifted exterior has the actual original split-cubic contraction. -/
@[reassoc] theorem coefficientShearResidueExteriorLift_toCurve :
    L ≫ pQ ≫ finiteGlobalContraction hπ data j hj =
      (slopeNormalizationIso a).inv ≫ originalResidueSplitCubic d hk hres := by
  rw [coefficientShearResidueExteriorLift_projection_assoc,
    coefficientShearResidueOrderedFinite, Category.assoc,
    originalResidueFiniteNormalization_splitCubic]

variable (ha : (a : AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) =
  (nodeTangentShear (W.map (residue R))).a₁)
local notation "σQ" => coefficientShearResidueTangentConjugation hπ data j hj
local notation "σA" => coefficientShearTangentConjugation hπ data j hj
local notation "P" => nodeTangentLineCoefficients V ≫ endpointReversal Q

include ha in
/-- The full ordered finite normalization is invariant under the actual source reflection. -/
@[reassoc] theorem coefficientShearResidueOrderedFinite_conjugation : P ≫ N = N := by
  have h : P ≫ (slopeNormalizationIso a).inv =
      (slopeNormalizationIso a).inv ≫ nodeTangentLineConjugation V := by
    apply (cancel_mono (slopeNormalizationIso a).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [nodeTangentLineConjugation_normalization V a ha, Iso.inv_hom_id_assoc]
  simp only [coefficientShearResidueOrderedFinite]
  rw [← Category.assoc, h, Category.assoc, originalResidueFiniteNormalization_conjugation]

include ha in
/-- The actual residue model conjugation gives the complete ordered exterior reflection. -/
@[reassoc] theorem coefficientShearResidueExteriorLift_conjugation : L ≫ σQ = P ≫ L := by
  apply (coefficientShearGlued_isPullback hπ data Q r j hj).hom_ext
  · rw [Category.assoc, coefficientShearResidueTangentConjugation_structure,
      coefficientShearResidueExteriorLift_structure_assoc, Category.assoc,
      coefficientShearResidueExteriorLift_structure, Category.assoc,
      endpointReversal_toBase, nodeTangentLineCoefficients_base]
    rfl
  · rw [Category.assoc, coefficientShearResidueTangentConjugation_projection,
      coefficientShearResidueExteriorLift_projection, Category.assoc,
      coefficientShearResidueExteriorLift_projection,
      coefficientShearResidueOrderedFinite_conjugation hπ data j hj d hk hres a ha]

end FLT.Mazur.WeierstrassDividedDepth

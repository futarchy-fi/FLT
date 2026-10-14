/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueExteriorLift

/-!
# The full split cubic determines the ordered residue exterior

The original coefficient leg and entire cubic contraction determine both the
integral-target map and its residue-tangent lift. No affine restriction is used.
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
local notation "L" => coefficientShearResidueExteriorLift hπ data j hj d hk hres a
local notation "c" => Spec.map (CommRingCat.ofHom (nodeTangentCoefficientMap W (residue R)))

/-- The complete original split cubic determines the ordered integral-target exterior. -/
theorem coefficientShearResidueOrderedExterior_unique
    (f : scheme Q ⟶ coefficientShearGlued hπ data A rA j hj)
    (hs : f ≫ sA = toBase Q ≫ c)
    (hc : f ≫ pA ≫ finiteGlobalContraction hπ data j hj =
      (slopeNormalizationIso a).inv ≫ originalResidueSplitCubic d hk hres) : f = F := by
  apply (cancel_epi (slopeNormalizationIso a).hom).mp
  rw [coefficientShearResidueOrderedExterior, Iso.hom_inv_id_assoc]
  apply coefficientShearResidueExterior_unique hπ data j hj d hk hres
  · rw [Category.assoc, hs, slopeNormalizationIso_base_assoc]
  · rw [Category.assoc, hc, Iso.hom_inv_id_assoc]

/-- Coefficient specialization of any full cubic lift recovers the original ordered exterior. -/
theorem coefficientShearResidueExteriorLift_unique_specialization
    (f : scheme Q ⟶ coefficientShearGlued hπ data Q r j hj)
    (hs : f ≫ sQ = toBase Q)
    (hc : f ≫ pQ ≫ finiteGlobalContraction hπ data j hj =
      (slopeNormalizationIso a).inv ≫ originalResidueSplitCubic d hk hres) : f ≫ M = F := by
  apply coefficientShearResidueOrderedExterior_unique hπ data j hj d hk hres a
  · rw [Category.assoc, coefficientShearTangentSpecialization,
      coefficientShearSpecialization_structure, ← Category.assoc, hs]
    rfl
  · simpa only [Category.assoc, coefficientShearTangentSpecialization,
      coefficientShearSpecialization_projection_assoc] using hc

/-- The coefficient field and whole original cubic determine the entire lifted exterior. -/
theorem coefficientShearResidueExteriorLift_unique
    (f : scheme Q ⟶ coefficientShearGlued hπ data Q r j hj)
    (hs : f ≫ sQ = toBase Q)
    (hc : f ≫ pQ ≫ finiteGlobalContraction hπ data j hj =
      (slopeNormalizationIso a).inv ≫ originalResidueSplitCubic d hk hres) : f = L := by
  apply (coefficientShearGlued_isPullback hπ data Q r j hj).hom_ext
  · rw [hs, coefficientShearResidueExteriorLift_structure]
  · have H : f ≫ M = L ≫ M :=
      (coefficientShearResidueExteriorLift_unique_specialization
        hπ data j hj d hk hres a f hs hc).trans
        (coefficientShearResidueExteriorLift_specialization hπ data j hj d hk hres a).symm
    have H' := congrArg (· ≫ pA) H
    simpa only [Category.assoc, coefficientShearTangentSpecialization,
      coefficientShearSpecialization_projection] using H'

end FLT.Mazur.WeierstrassDividedDepth

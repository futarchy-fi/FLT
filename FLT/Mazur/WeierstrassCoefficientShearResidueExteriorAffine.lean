/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialLineContraction
public import FLT.Mazur.WeierstrassResidueIncidenceNormalization
public import FLT.Mazur.WeierstrassCoefficientShearResidueExteriorLift

/-!
# The actual nonsplit exterior retains the entire initial incidence line

Regularity of the original horizontal coordinate identifies the affine part of
the proper lift, including both ordered node preimages, in the actual target.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open ProjectiveLine WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (hstart : 0 < start) (hres : residue R π = 0)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "hk" => show 0 < start + (0 : Fin (n + 1)).val from by dsimp; omega
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
  (hs : algebraMap R (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (π ^ start) = 0)
  (h3 : algebraMap R (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (data ⟨0, Nat.zero_lt_succ n⟩).b3 = 0)
  (h4 : algebraMap R (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (data ⟨0, Nat.zero_lt_succ n⟩).b4 = 0)
local notation "hr" => residueTangentEquation_root W
local notation "L" => coefficientShearInitialLine hπ data Q r j hj hs h3 h4 hr
local notation "p" => coefficientShearGluedProjection hπ data Q r j hj
local notation "g" => coefficientShearGluedStructure hπ data Q r j hj
local notation "N" => originalResidueFiniteNormalization hπ data j hj d hk hres

/-- The whole initial incidence line is the affine restriction of the original proper lift. -/
@[reassoc] theorem coefficientShearResidueInitialLine_projection :
    L ≫ p = left Q ≫ N := by
  apply finiteGlobalContraction_ext_of_regular_x hπ data j hj
    (originalResidueNormalization d hk hres)
    (originalResidueNormalization_x_regular d hk hres)
  · rw [Category.assoc, coefficientShearInitialLine_toCurve]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q) ≫
      WeierstrassIntegralChart.integralCurveChart W 2)
      (originalShearIncidenceNormalization_eq_residue d hk hres hs h3 h4)
  · rw [Category.assoc, originalResidueFiniteNormalization_contraction,
      originalResidueCompleteNormalization_left]
    rfl

variable (a : (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))ˣ)
local notation "F" => coefficientShearResidueExteriorLift hπ data j hj d hk hres a

/-- The complete incidence line, including both node origins, lies in the actual exterior. -/
@[reassoc] theorem coefficientShearResidueExteriorLift_affine :
    left Q ≫ (slopeNormalizationIso a).hom ≫ F = L := by
  apply (coefficientShearGlued_isPullback hπ data Q r j hj).hom_ext
  · simp only [Category.assoc]
    rw [coefficientShearResidueExteriorLift_structure,
      slopeNormalizationIso_base, left_toBase, coefficientShearInitialLine_structure]
    rfl
  · simp only [Category.assoc]
    rw [coefficientShearResidueExteriorLift_projection,
      coefficientShearResidueOrderedFinite, Iso.hom_inv_id_assoc,
      coefficientShearResidueInitialLine_projection hπ data j hj hstart hres hs h3 h4]

end FLT.Mazur.WeierstrassDividedDepth

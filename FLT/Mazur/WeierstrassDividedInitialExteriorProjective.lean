/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialExteriorLaurent
public import FLT.Mazur.ProjectiveLineInfinityTorusGluing
public import FLT.Mazur.ProjectiveLineEndpoints

/-!
# The actual initial exterior component is a projective line

The comparison retains the full original incidence and infinity charts,
the residue coefficient structure, and the ordered node markings 0 and -a₁.
No projective-line comparison is assumed as input.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hstart : 0 < start) (hk : 2 * start ≤ depth) (hdepth : 0 < depth)
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "u" => Units.mk0 a (IsUnit.ne_zero (residue_tangent_isUnit D))
local notation "E" => initialExteriorCurve hπ data D j hj hstart hk
local notation "l" => initialExteriorAffineChart hπ data D j hj hstart hk
local notation "r" => initialExteriorLaurentChart hπ data D j hj hstart hk hdepth
local notation "e" => initialExteriorLaurentGluingIso hπ data D j hj hstart hk hdepth

/-- The actual exterior component, with its original charts, is the fixed projective line. -/
def initialExteriorProjectiveIso : E ≅ ProjectiveLine.scheme K :=
  (e).symm ≪≫ ProjectiveLine.infinityTorusGluingIso u

/-- The comparison retains the entire original affine incidence coordinate. -/
@[reassoc] theorem initialExteriorProjectiveIso_affine :
    l ≫ (initialExteriorProjectiveIso hπ data D j hj hstart hk hdepth).hom =
      ProjectiveLine.left K := by
  rw [← initialExteriorLaurentGluingIso_affine hπ data D j hj hstart hk hdepth]
  simp only [initialExteriorProjectiveIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact ProjectiveLine.infinityTorusGluingIso_left u

/-- The full original infinity torus keeps w=a₁⁻¹(T-1), rather than a pointwise surrogate. -/
@[reassoc] theorem initialExteriorProjectiveIso_laurent :
    r ≫ (initialExteriorProjectiveIso hπ data D j hj hstart hk hdepth).hom =
      ProjectiveLine.infinityTorusChart u := by
  rw [← initialExteriorLaurentGluingIso_infinity hπ data D j hj hstart hk hdepth]
  simp only [initialExteriorProjectiveIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact ProjectiveLine.infinityTorusGluingIso_right u

/-- The inverse comparison retains the original complete incidence line. -/
@[reassoc] theorem initialExteriorProjectiveIso_inv_affine :
    ProjectiveLine.left K ≫
      (initialExteriorProjectiveIso hπ data D j hj hstart hk hdepth).inv = l := by
  rw [← initialExteriorProjectiveIso_affine hπ data D j hj hstart hk hdepth,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The inverse comparison retains the original entire infinity torus. -/
@[reassoc] theorem initialExteriorProjectiveIso_inv_laurent :
    ProjectiveLine.infinityTorusChart u ≫
      (initialExteriorProjectiveIso hπ data D j hj hstart hk hdepth).inv = r := by
  rw [← initialExteriorProjectiveIso_laurent hπ data D j hj hstart hk hdepth,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The isomorphism is over the actual residue field of the original model. -/
@[reassoc] theorem initialExteriorProjectiveIso_structure :
    (initialExteriorProjectiveIso hπ data D j hj hstart hk hdepth).hom ≫
      ProjectiveLine.toBase K = initialExteriorStructure hπ data D j hj hstart hk := by
  apply (cancel_epi (e).hom).mp
  apply pushout.hom_ext
  · simp only [← Category.assoc, initialExteriorLaurentGluingIso_affine,
      initialExteriorProjectiveIso_affine, ProjectiveLine.left_toBase,
      initialExteriorStructure_affine]
    rfl
  · simp only [← Category.assoc, initialExteriorLaurentGluingIso_infinity,
      initialExteriorProjectiveIso_laurent, ProjectiveLine.infinityTorusChart_toBase,
      initialExteriorLaurentChart_structure]
    rfl

/-- The projective line maps to the actual retained global fiber through its proved component. -/
def initialProjectiveToGlobal : ProjectiveLine.scheme K ⟶
    finiteGlobalTensorModel hπ data K j hj :=
  (initialExteriorProjectiveIso hπ data D j hj hstart hk hdepth).inv ≫
    initialExteriorToGlobal hπ data D j hj hstart hk

/-- Its left chart is the original incidence line in the retained global fiber. -/
@[reassoc] theorem initialProjectiveToGlobal_affine :
    ProjectiveLine.left K ≫ initialProjectiveToGlobal hπ data D j hj hstart hk hdepth =
      initialGlobalIncidenceLine hπ data D j hj hstart hk := by
  rw [initialProjectiveToGlobal, initialExteriorProjectiveIso_inv_affine_assoc,
    initialExteriorToGlobal_affine]

/-- The first ordered projective marking is exactly the original first initial node. -/
@[reassoc] theorem initialProjectiveToGlobal_first :
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (0 : K)).toRingHom) ≫
      ProjectiveLine.left K ≫ initialProjectiveToGlobal hπ data D j hj hstart hk hdepth =
        initialGlobalFirstSection hπ data D j hj hstart hk := by
  rw [initialProjectiveToGlobal_affine, initialGlobalIncidenceLine_first]

/-- The second ordered marking is the actual second node, with original slope minus a₁. -/
@[reassoc] theorem initialProjectiveToGlobal_second :
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (-a)).toRingHom) ≫
      ProjectiveLine.left K ≫ initialProjectiveToGlobal hπ data D j hj hstart hk hdepth =
        initialGlobalSecondSection hπ data D j hj hstart hk := by
  rw [initialProjectiveToGlobal_affine, initialGlobalIncidenceLine_second]

end FLT.Mazur.WeierstrassDividedDepth

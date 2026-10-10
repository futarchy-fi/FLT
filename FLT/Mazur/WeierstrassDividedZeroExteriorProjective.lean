/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroExteriorLaurent
public import FLT.Mazur.ProjectiveLineInfinityTorusGluing
public import FLT.Mazur.ProjectiveLineEndpoints

/-!
# The actual retained start-zero exterior is a projective line

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
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "u" => Units.mk0 a (IsUnit.ne_zero (D.a₁_unit.map (residue R)))
local notation "E" => zeroRetainedExteriorCurve hπ data D j hj r hr hk0 hk
local notation "l" => zeroRetainedExteriorAffineChart hπ data D j hj r hr hk0 hk
local notation "lc" => zeroRetainedExteriorLaurentChart hπ data D j hj r hr hk0 hk
local notation "e" => zeroRetainedExteriorLaurentGluingIso hπ data D j hj r hr hk0 hk

/-- The actual exterior component, with its original charts, is the fixed projective line. -/
def zeroRetainedExteriorProjectiveIso : E ≅ ProjectiveLine.scheme K :=
  (e).symm ≪≫ ProjectiveLine.infinityTorusGluingIso u

/-- The comparison retains the entire original affine incidence coordinate. -/
@[reassoc] theorem zeroRetainedExteriorProjectiveIso_affine :
    l ≫ (zeroRetainedExteriorProjectiveIso hπ data D j hj r hr hk0 hk).hom =
      ProjectiveLine.left K := by
  rw [← zeroRetainedExteriorLaurentGluingIso_affine hπ data D j hj r hr hk0 hk]
  simp only [zeroRetainedExteriorProjectiveIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact ProjectiveLine.infinityTorusGluingIso_left u

/-- The full original infinity torus keeps w=a₁⁻¹(T-1), rather than a pointwise surrogate. -/
@[reassoc] theorem zeroRetainedExteriorProjectiveIso_laurent :
    lc ≫ (zeroRetainedExteriorProjectiveIso hπ data D j hj r hr hk0 hk).hom =
      ProjectiveLine.infinityTorusChart u := by
  rw [← zeroRetainedExteriorLaurentGluingIso_infinity hπ data D j hj r hr hk0 hk]
  simp only [zeroRetainedExteriorProjectiveIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact ProjectiveLine.infinityTorusGluingIso_right u

/-- The inverse comparison retains the original complete incidence line. -/
@[reassoc] theorem zeroRetainedExteriorProjectiveIso_inv_affine :
    ProjectiveLine.left K ≫
      (zeroRetainedExteriorProjectiveIso hπ data D j hj r hr hk0 hk).inv = l := by
  rw [← zeroRetainedExteriorProjectiveIso_affine hπ data D j hj r hr hk0 hk,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The inverse comparison retains the original entire infinity torus. -/
@[reassoc] theorem zeroRetainedExteriorProjectiveIso_inv_laurent :
    ProjectiveLine.infinityTorusChart u ≫
      (zeroRetainedExteriorProjectiveIso hπ data D j hj r hr hk0 hk).inv = lc := by
  rw [← zeroRetainedExteriorProjectiveIso_laurent hπ data D j hj r hr hk0 hk,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The isomorphism is over the actual residue field of the original model. -/
@[reassoc] theorem zeroRetainedExteriorProjectiveIso_structure :
    (zeroRetainedExteriorProjectiveIso hπ data D j hj r hr hk0 hk).hom ≫
      ProjectiveLine.toBase K = zeroRetainedExteriorStructure hπ data D j hj r hr hk0 hk := by
  apply (cancel_epi (e).hom).mp
  apply pushout.hom_ext
  · simp only [← Category.assoc, zeroRetainedExteriorLaurentGluingIso_affine,
      zeroRetainedExteriorProjectiveIso_affine, ProjectiveLine.left_toBase,
      zeroRetainedExteriorStructure_affine]
    rfl
  · simp only [← Category.assoc, zeroRetainedExteriorLaurentGluingIso_infinity,
      zeroRetainedExteriorProjectiveIso_laurent, ProjectiveLine.infinityTorusChart_toBase,
      zeroRetainedExteriorLaurentChart_structure]
    rfl

/-- The projective line maps to the actual retained global fiber through its proved component. -/
def zeroRetainedProjectiveToGlobal : ProjectiveLine.scheme K ⟶
    finiteGlobalTensorModel hπ data K (j + 1 + r) hr :=
  (zeroRetainedExteriorProjectiveIso hπ data D j hj r hr hk0 hk).inv ≫
    zeroRetainedExteriorToGlobal hπ data D j hj r hr hk0 hk

/-- Its left chart is the original incidence line in the retained global fiber. -/
@[reassoc] theorem zeroRetainedProjectiveToGlobal_affine :
    ProjectiveLine.left K ≫ zeroRetainedProjectiveToGlobal hπ data D j hj r hr hk0 hk =
      olderGlobalZeroIncidence hπ data D j hj r hr hk0 hk := by
  rw [zeroRetainedProjectiveToGlobal, zeroRetainedExteriorProjectiveIso_inv_affine_assoc,
    zeroRetainedExteriorToGlobal_affine]

/-- The first ordered projective marking is exactly the original first retained start-zero node. -/
@[reassoc] theorem zeroRetainedProjectiveToGlobal_first :
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (0 : K)).toRingHom) ≫
      ProjectiveLine.left K ≫ zeroRetainedProjectiveToGlobal hπ data D j hj r hr hk0 hk =
        olderGlobalZeroFirstSection hπ data D j hj r hr hk0 hk := by
  rw [zeroRetainedProjectiveToGlobal_affine, zeroRetainedIncidence_first]

/-- The second ordered marking is the actual second node, with original slope minus a₁. -/
@[reassoc] theorem zeroRetainedProjectiveToGlobal_second :
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (-a)).toRingHom) ≫
      ProjectiveLine.left K ≫ zeroRetainedProjectiveToGlobal hπ data D j hj r hr hk0 hk =
        olderGlobalZeroSecondSection hπ data D j hj r hr hk0 hk := by
  rw [zeroRetainedProjectiveToGlobal_affine, zeroRetainedIncidence_second]

end FLT.Mazur.WeierstrassDividedDepth

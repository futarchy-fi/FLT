/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityResidueZero
public import FLT.Mazur.WeierstrassDividedInfinityLaurentChart
public import FLT.Mazur.WeierstrassDividedGlobalFiniteZero

/-!
# The retained finite-model zero is Laurent parameter one

Both projections identify the original base-changed section in the actual
residue pullback; the section is not replaced by a new choice of origin.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing MonoidalCategory MonObj
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hdepth : 0 < depth) (j : ℕ) (hj : j ≤ n)
open WeierstrassIntegralChart
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data j hj

/-- Parameter one projects to the original integral section at every finite stage. -/
@[reassoc] theorem infinityLaurentChart_one_projection :
    η[MultiplicativeGroupScheme.gm K].left ≫
        infinityLaurentChart hπ data D hdepth j hj ≫ pullback.snd q f =
      q ≫ finiteGlobalZero hπ data j hj := by
  rw [infinityLaurentChart, Category.assoc]
  have h := (finiteInfinityTensorChart_isPullback hπ data K j hj).w
  rw [h, infinityResidueIso_one_projection_assoc]
  rfl

/-- The entire original zero section is the identity in the retained Laurent chart. -/
theorem infinityLaurentChart_one :
    η[MultiplicativeGroupScheme.gm K].left ≫
        infinityLaurentChart hπ data D hdepth j hj =
      finiteGlobalBaseChangeZero hπ data j hj q ≫ (pullbackSymmetry f q).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, infinityLaurentChart_structure]
    rw [η[MultiplicativeGroupScheme.gm K].w]
    simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
      finiteGlobalBaseChangeZero_structure]
    rfl
  · rw [Category.assoc, infinityLaurentChart_one_projection]
    simp only [Category.assoc, pullbackSymmetry_hom_comp_snd,
      finiteGlobalBaseChangeZero, pullback.lift_fst]

end FLT.Mazur.WeierstrassDividedDepth

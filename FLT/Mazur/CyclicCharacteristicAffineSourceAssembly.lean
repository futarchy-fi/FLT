/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineSourceCover
public import FLT.Mazur.SchemeDisjointOpenPair

/-!
# Assembling maps on the original characteristic source domain

The selected normalized chart and opposite overlap are disjoint open charts
covering the original source domain. Their actual coproduct is isomorphic to
that domain, so any pair of scheme maps assembles uniquely there.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool)
  (j : (invariantAffineCover n (!b)).I₀)

/-- The two component images in the original source domain are disjoint. -/
theorem affineSource_images_disjoint :
    Disjoint (Set.range (selectedToAffineSource n b j))
      (Set.range (oppositeToAffineSource n b j)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx⟩ ⟨y, hy⟩
  have he := congrArg ((affineSourceOpen n b j).ι) (hx.trans hy.symm)
  change (selectedToAffineSource n b j ≫ (affineSourceOpen n b j).ι) x =
    (oppositeToAffineSource n b j ≫ (affineSourceOpen n b j).ι) y at he
  rw [selectedToAffineSource_comp, oppositeToAffineSource_comp,
    Scheme.Hom.comp_apply] at he
  have hb : (!b) = b := congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp he)
  cases b <;> cases hb

/-- The original source domain is reached from the coproduct of its two actual chart schemes. -/
def affineSourcePairMap :
    invariantAffineChart n ⟨!b, j⟩ ⨿ (affineOppositeOpen n b j).toScheme ⟶
      (affineSourceOpen n b j).toScheme :=
  coprod.desc (selectedToAffineSource n b j) (oppositeToAffineSource n b j)

instance affineSourcePairMap_isOpenImmersion : IsOpenImmersion (affineSourcePairMap n b j) :=
  SchemeDisjointOpenPair.desc_isOpenImmersion _ _ (affineSource_images_disjoint n b j)

/-- The pair map covers the entire original characteristic source domain. -/
instance affineSourcePairMap_surjective : Surjective (affineSourcePairMap n b j) := by
  constructor
  intro x
  obtain ⟨c, y, hy⟩ := affineSourceChartMap_covers n b j x
  cases c
  · refine ⟨(coprod.inl : invariantAffineChart n ⟨!b, j⟩ ⟶
      invariantAffineChart n ⟨!b, j⟩ ⨿ (affineOppositeOpen n b j).toScheme) y, ?_⟩
    exact (congrArg (fun f => f y) (coprod.inl_desc
      (selectedToAffineSource n b j) (oppositeToAffineSource n b j))).trans hy
  · refine ⟨(coprod.inr : (affineOppositeOpen n b j).toScheme ⟶
      invariantAffineChart n ⟨!b, j⟩ ⨿ (affineOppositeOpen n b j).toScheme) y, ?_⟩
    exact (congrArg (fun f => f y) (coprod.inr_desc
      (selectedToAffineSource n b j) (oppositeToAffineSource n b j))).trans hy

/-- The decomposition is an isomorphism of schemes, not just a partition of points. -/
instance affineSourcePairMap_isIso : IsIso (affineSourcePairMap n b j) := by
  let _ : Epi (affineSourcePairMap n b j).base :=
    (TopCat.epi_iff_surjective _).mpr (affineSourcePairMap n b j).surjective
  exact IsOpenImmersion.isIso _

/-- Assemble any maps on the actual selected chart and opposite overlap. -/
def affineSourceAssemble {Y : Scheme} (f : invariantAffineChart n ⟨!b, j⟩ ⟶ Y)
    (g : (affineOppositeOpen n b j).toScheme ⟶ Y) : (affineSourceOpen n b j).toScheme ⟶ Y :=
  inv (affineSourcePairMap n b j) ≫ coprod.desc f g

/-- Assembly retains the prescribed map on the selected original chart. -/
@[reassoc] theorem affineSourceAssemble_selected {Y : Scheme}
    (f : invariantAffineChart n ⟨!b, j⟩ ⟶ Y) (g : (affineOppositeOpen n b j).toScheme ⟶ Y) :
    selectedToAffineSource n b j ≫ affineSourceAssemble n b j f g = f := by
  have h : (coprod.inl : invariantAffineChart n ⟨!b, j⟩ ⟶ _ ) ≫ affineSourcePairMap n b j =
      selectedToAffineSource n b j := coprod.inl_desc _ _
  rw [affineSourceAssemble, ← h, Category.assoc, IsIso.hom_inv_id_assoc, coprod.inl_desc]

/-- Assembly retains the reconstructed map on the opposite original overlap. -/
@[reassoc] theorem affineSourceAssemble_opposite {Y : Scheme}
    (f : invariantAffineChart n ⟨!b, j⟩ ⟶ Y) (g : (affineOppositeOpen n b j).toScheme ⟶ Y) :
    oppositeToAffineSource n b j ≫ affineSourceAssemble n b j f g = g := by
  have h : (coprod.inr : (affineOppositeOpen n b j).toScheme ⟶ _) ≫ affineSourcePairMap n b j =
      oppositeToAffineSource n b j := coprod.inr_desc _ _
  rw [affineSourceAssemble, ← h, Category.assoc, IsIso.hom_inv_id_assoc, coprod.inr_desc]

/-- The two original component maps determine the assembled morphism uniquely. -/
theorem affineSourceAssemble_unique {Y : Scheme}
    (f : invariantAffineChart n ⟨!b, j⟩ ⟶ Y) (g : (affineOppositeOpen n b j).toScheme ⟶ Y)
    (k : (affineSourceOpen n b j).toScheme ⟶ Y)
    (hf : selectedToAffineSource n b j ≫ k = f)
    (hg : oppositeToAffineSource n b j ≫ k = g) :
    k = affineSourceAssemble n b j f g := by
  apply (cancel_epi (affineSourcePairMap n b j)).mp
  apply coprod.hom_ext
  · simpa only [← Category.assoc, affineSourcePairMap, coprod.inl_desc] using
      hf.trans (affineSourceAssemble_selected n b j f g).symm
  · simpa only [← Category.assoc, affineSourcePairMap, coprod.inr_desc] using
      hg.trans (affineSourceAssemble_opposite n b j f g).symm

end FLT.Mazur.CyclicCharacteristicOrbit

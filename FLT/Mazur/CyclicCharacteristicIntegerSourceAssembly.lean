/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicIntegerSourceCover
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

/-- The two component images in the original source domain are disjoint. -/
theorem integerSource_images_disjoint :
    Disjoint (Set.range (selectedToIntegerSource n b))
      (Set.range (oppositeToIntegerSource n b)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx⟩ ⟨y, hy⟩
  have he := congrArg ((integerSourceOpen n b).ι) (hx.trans hy.symm)
  change (selectedToIntegerSource n b ≫ (integerSourceOpen n b).ι) x =
    (oppositeToIntegerSource n b ≫ (integerSourceOpen n b).ι) y at he
  rw [selectedToIntegerSource_comp, oppositeToIntegerSource_comp,
    Scheme.Hom.comp_apply] at he
  have hb : (!b) = b := congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp he)
  cases b <;> cases hb

/-- The original source domain is reached from the coproduct of its two actual chart schemes. -/
def integerSourcePairMap :
    normalizedLocus n (!b) ⨿ (transitionOpen n b).toScheme ⟶
      (integerSourceOpen n b).toScheme :=
  coprod.desc (selectedToIntegerSource n b) (oppositeToIntegerSource n b)

instance integerSourcePairMap_isOpenImmersion : IsOpenImmersion (integerSourcePairMap n b) :=
  SchemeDisjointOpenPair.desc_isOpenImmersion _ _ (integerSource_images_disjoint n b)

/-- The pair map covers the entire original characteristic source domain. -/
instance integerSourcePairMap_surjective : Surjective (integerSourcePairMap n b) := by
  constructor
  intro x
  obtain ⟨c, y, hy⟩ := integerSourceChartMap_covers n b x
  cases c
  · refine ⟨(coprod.inl : normalizedLocus n (!b) ⟶
      normalizedLocus n (!b) ⨿ (transitionOpen n b).toScheme) y, ?_⟩
    exact (congrArg (fun f => f y) (coprod.inl_desc
      (selectedToIntegerSource n b) (oppositeToIntegerSource n b))).trans hy
  · refine ⟨(coprod.inr : (transitionOpen n b).toScheme ⟶
      normalizedLocus n (!b) ⨿ (transitionOpen n b).toScheme) y, ?_⟩
    exact (congrArg (fun f => f y) (coprod.inr_desc
      (selectedToIntegerSource n b) (oppositeToIntegerSource n b))).trans hy

/-- The decomposition is an isomorphism of schemes, not just a partition of points. -/
instance integerSourcePairMap_isIso : IsIso (integerSourcePairMap n b) := by
  let _ : Epi (integerSourcePairMap n b).base :=
    (TopCat.epi_iff_surjective _).mpr (integerSourcePairMap n b).surjective
  exact IsOpenImmersion.isIso _

/-- Assemble any maps on the actual selected chart and opposite overlap. -/
def integerSourceAssemble {Y : Scheme} (f : normalizedLocus n (!b) ⟶ Y)
    (g : (transitionOpen n b).toScheme ⟶ Y) : (integerSourceOpen n b).toScheme ⟶ Y :=
  inv (integerSourcePairMap n b) ≫ coprod.desc f g

/-- Assembly retains the prescribed map on the selected original chart. -/
@[reassoc] theorem integerSourceAssemble_selected {Y : Scheme}
    (f : normalizedLocus n (!b) ⟶ Y) (g : (transitionOpen n b).toScheme ⟶ Y) :
    selectedToIntegerSource n b ≫ integerSourceAssemble n b f g = f := by
  have h : (coprod.inl : normalizedLocus n (!b) ⟶ _ ) ≫ integerSourcePairMap n b =
      selectedToIntegerSource n b := coprod.inl_desc _ _
  rw [integerSourceAssemble, ← h, Category.assoc, IsIso.hom_inv_id_assoc, coprod.inl_desc]

/-- Assembly retains the reconstructed map on the opposite original overlap. -/
@[reassoc] theorem integerSourceAssemble_opposite {Y : Scheme}
    (f : normalizedLocus n (!b) ⟶ Y) (g : (transitionOpen n b).toScheme ⟶ Y) :
    oppositeToIntegerSource n b ≫ integerSourceAssemble n b f g = g := by
  have h : (coprod.inr : (transitionOpen n b).toScheme ⟶ _) ≫ integerSourcePairMap n b =
      oppositeToIntegerSource n b := coprod.inr_desc _ _
  rw [integerSourceAssemble, ← h, Category.assoc, IsIso.hom_inv_id_assoc, coprod.inr_desc]

/-- The two original component maps determine the assembled morphism uniquely. -/
theorem integerSourceAssemble_unique {Y : Scheme}
    (f : normalizedLocus n (!b) ⟶ Y) (g : (transitionOpen n b).toScheme ⟶ Y)
    (k : (integerSourceOpen n b).toScheme ⟶ Y)
    (hf : selectedToIntegerSource n b ≫ k = f)
    (hg : oppositeToIntegerSource n b ≫ k = g) :
    k = integerSourceAssemble n b f g := by
  apply (cancel_epi (integerSourcePairMap n b)).mp
  apply coprod.hom_ext
  · simpa only [← Category.assoc, integerSourcePairMap, coprod.inl_desc] using
      hf.trans (integerSourceAssemble_selected n b f g).symm
  · simpa only [← Category.assoc, integerSourcePairMap, coprod.inr_desc] using
      hg.trans (integerSourceAssemble_opposite n b f g).symm

end FLT.Mazur.CyclicCharacteristicOrbit

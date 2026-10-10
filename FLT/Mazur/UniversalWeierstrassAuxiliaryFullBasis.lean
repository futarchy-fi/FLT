/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryTorsionCover

/-!
# The auxiliary marking is a full scheme-theoretic basis

The original label sections identify the constant label scheme over level four
with the entire four-torsion scheme. Both the isomorphism and its compatibility
with the original cubic come from the actual markings.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

/-- The constant label scheme over the auxiliary level scheme. -/
def auxiliaryConstantLabels : Scheme := ∐ fun _ : Labels 4 ↦ levelFour.left

/-- Its structure map retains the auxiliary base point on every component. -/
def auxiliaryConstantLabelsMap : auxiliaryConstantLabels ⟶ levelFour.left :=
  Sigma.desc fun _ ↦ 𝟙 _

/-- The full labeling map, built from the original marked sections. -/
def auxiliaryFullBasisMap : auxiliaryConstantLabels ⟶ auxiliaryFourTorsion :=
  Sigma.desc auxiliaryTorsionSection

/-- The full labeling map is an open immersion because different labels are disjoint. -/
instance auxiliaryFullBasisMap_open : IsOpenImmersion auxiliaryFullBasisMap :=
  isOpenImmersion_sigmaDesc _ _ auxiliaryTorsionSection_disjoint

/-- Every point belongs to the full labeling map's image. -/
theorem auxiliaryFullBasisMap_range : auxiliaryFullBasisMap.opensRange = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, y, rfl⟩ := auxiliaryTorsionSection_covers x
  refine ⟨Sigma.ι (fun _ : Labels 4 ↦ levelFour.left) a y, ?_⟩
  exact congrArg (fun f : levelFour.left ⟶ auxiliaryFourTorsion ↦ f y)
    (Sigma.ι_comp_desc auxiliaryTorsionSection a)

/-- The marking identifies the full torsion scheme, including its scheme structure. -/
instance auxiliaryFullBasisMap_isIso : IsIso auxiliaryFullBasisMap :=
  isIso_of_isOpenImmersion_of_opensRange_eq_top _ auxiliaryFullBasisMap_range

/-- The full scheme-theoretic auxiliary basis. -/
def auxiliaryFullBasis : auxiliaryConstantLabels ≅ auxiliaryFourTorsion :=
  asIso auxiliaryFullBasisMap

/-- The basis is an isomorphism over the original auxiliary level scheme. -/
@[reassoc (attr := simp)] theorem auxiliaryFullBasis_base :
    auxiliaryFullBasis.hom ≫ auxiliaryFourTorsionMap = auxiliaryConstantLabelsMap := by
  apply Sigma.hom_ext
  intro a
  simp only [auxiliaryFullBasis, auxiliaryFullBasisMap, asIso_hom, Sigma.ι_comp_desc_assoc,
    auxiliaryTorsionSection_map, auxiliaryConstantLabelsMap, Sigma.ι_comp_desc]

/-- The component labeled by a is exactly the originally constructed torsion section. -/
@[reassoc (attr := simp)] theorem auxiliaryFullBasis_component (a : Labels 4) :
    Sigma.ι (fun _ : Labels 4 ↦ levelFour.left) a ≫ auxiliaryFullBasis.hom =
      auxiliaryTorsionSection a := Sigma.ι_comp_desc _ _

/-- Maps out of the full torsion scheme are determined by the auxiliary sections. -/
theorem auxiliaryTorsionSection_hom_ext {Y : Scheme} (f g : auxiliaryFourTorsion ⟶ Y)
    (h : ∀ a, auxiliaryTorsionSection a ≫ f = auxiliaryTorsionSection a ≫ g) : f = g := by
  apply (cancel_epi auxiliaryFullBasis.hom).mp
  apply Sigma.hom_ext
  intro a
  simpa only [auxiliaryFullBasis_component_assoc] using h a

/-- Any endomorphism fixing all labels fixes the entire torsion scheme. -/
theorem auxiliaryTorsion_end_eq_id (f : auxiliaryFourTorsion ⟶ auxiliaryFourTorsion)
    (h : ∀ a, auxiliaryTorsionSection a ≫ f = auxiliaryTorsionSection a) : f = 𝟙 _ := by
  apply auxiliaryTorsionSection_hom_ext
  intro a
  simpa only [Category.comp_id] using h a

end FLT.Mazur.UniversalWeierstrass

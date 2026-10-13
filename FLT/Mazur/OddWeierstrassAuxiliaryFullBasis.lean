/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryTorsionCover

/-!
# The auxiliary marking is a full scheme-theoretic basis

The original label sections identify the constant label scheme over level three
with the entire three-torsion scheme. Both the isomorphism and its compatibility
with the original cubic come from the actual markings.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.OddWeierstrassParameter

open IntegralWeierstrassParameter (OddChartRing)
open UniversalWeierstrass (Labels labels_pow)

/-- The constant label scheme over the auxiliary level scheme. -/
def auxiliaryConstantLabels : Scheme := ∐ fun _ : Labels 3 ↦ levelThree.left

/-- Its structure map retains the auxiliary base point on every component. -/
def auxiliaryConstantLabelsMap : auxiliaryConstantLabels ⟶ levelThree.left :=
  Sigma.desc fun _ ↦ 𝟙 _

/-- The full labeling map, built from the original marked sections. -/
def auxiliaryFullBasisMap : auxiliaryConstantLabels ⟶ auxiliaryThreeTorsion :=
  Sigma.desc auxiliaryTorsionSection

/-- The full labeling map is an open immersion because different labels are disjoint. -/
instance auxiliaryFullBasisMap_open : IsOpenImmersion auxiliaryFullBasisMap :=
  isOpenImmersion_sigmaDesc _ _ auxiliaryTorsionSection_disjoint

/-- Every point belongs to the full labeling map's image. -/
theorem auxiliaryFullBasisMap_range : auxiliaryFullBasisMap.opensRange = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, y, rfl⟩ := auxiliaryTorsionSection_covers x
  refine ⟨Sigma.ι (fun _ : Labels 3 ↦ levelThree.left) a y, ?_⟩
  exact congrArg (fun f : levelThree.left ⟶ auxiliaryThreeTorsion ↦ f y)
    (Sigma.ι_comp_desc auxiliaryTorsionSection a)

/-- The marking identifies the full torsion scheme, including its scheme structure. -/
instance auxiliaryFullBasisMap_isIso : IsIso auxiliaryFullBasisMap :=
  isIso_of_isOpenImmersion_of_opensRange_eq_top _ auxiliaryFullBasisMap_range

/-- The full scheme-theoretic auxiliary basis. -/
def auxiliaryFullBasis : auxiliaryConstantLabels ≅ auxiliaryThreeTorsion :=
  asIso auxiliaryFullBasisMap

/-- The basis is an isomorphism over the original auxiliary level scheme. -/
@[reassoc (attr := simp)] theorem auxiliaryFullBasis_base :
    auxiliaryFullBasis.hom ≫ auxiliaryThreeTorsionMap = auxiliaryConstantLabelsMap := by
  apply Sigma.hom_ext
  intro a
  simp only [auxiliaryFullBasis, auxiliaryFullBasisMap, asIso_hom, Sigma.ι_comp_desc_assoc,
    auxiliaryTorsionSection_map, auxiliaryConstantLabelsMap, Sigma.ι_comp_desc]

/-- The component labeled by a is exactly the originally constructed torsion section. -/
@[reassoc (attr := simp)] theorem auxiliaryFullBasis_component (a : Labels 3) :
    Sigma.ι (fun _ : Labels 3 ↦ levelThree.left) a ≫ auxiliaryFullBasis.hom =
      auxiliaryTorsionSection a := Sigma.ι_comp_desc _ _

/-- Maps out of the full torsion scheme are determined by the auxiliary sections. -/
theorem auxiliaryTorsionSection_hom_ext {Y : Scheme} (f g : auxiliaryThreeTorsion ⟶ Y)
    (h : ∀ a, auxiliaryTorsionSection a ≫ f = auxiliaryTorsionSection a ≫ g) : f = g := by
  apply (cancel_epi auxiliaryFullBasis.hom).mp
  apply Sigma.hom_ext
  intro a
  simpa only [auxiliaryFullBasis_component_assoc] using h a

/-- Any endomorphism fixing all labels fixes the entire torsion scheme. -/
theorem auxiliaryTorsion_end_eq_id (f : auxiliaryThreeTorsion ⟶ auxiliaryThreeTorsion)
    (h : ∀ a, auxiliaryTorsionSection a ≫ f = auxiliaryTorsionSection a) : f = 𝟙 _ := by
  apply auxiliaryTorsionSection_hom_ext
  intro a
  simpa only [Category.comp_id] using h a

end FLT.Mazur.OddWeierstrassParameter

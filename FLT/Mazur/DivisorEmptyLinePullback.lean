/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierIdealPullbackComparison
public import FLT.Mazur.DivisorLineSectionCompatibility
public import FLT.Mazur.DivisorCanonicalOperations

/-!
# Canonical empty-divisor lines and their unit frames under pullback

The unit ideal remains Cartier under every scheme morphism. The canonical
positive-line comparison retains the unit frame of the empty divisor.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLinePullbackIsoOfEq
variable {X Y : Scheme} (f : X ⟶ Y)

/-- The canonical empty-divisor comparison for an arbitrary scheme morphism. -/
irreducible_def divisorEmptyLinePullbackIso :
    (pullback f).obj (divisorLineBundle ⊤ effectiveCartier_top) ≅
      divisorLineBundle ⊤ effectiveCartier_top := by
  let _ := idealModulePullbackHom_isIso_of_cartier f effectiveCartier_top
    ((Scheme.IdealSheafData.comap_top f).symm ▸ effectiveCartier_top)
  exact divisorLinePullbackIsoOfEq f effectiveCartier_top effectiveCartier_top
    (Scheme.IdealSheafData.comap_top f)

/-- The empty-divisor comparison preserves the actual canonical section. -/
theorem divisorEmptyLinePullbackIso_section :
    DivisorLineSectionCompatible f effectiveCartier_top effectiveCartier_top
      (divisorEmptyLinePullbackIso f) := by
  let _ := idealModulePullbackHom_isIso_of_cartier f effectiveCartier_top
    ((Scheme.IdealSheafData.comap_top f).symm ▸ effectiveCartier_top)
  rw [divisorEmptyLinePullbackIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- A section-preserving empty-divisor target comparison gives its canonical unit frame. -/
@[reassoc] theorem DivisorLineSectionCompatible.unit {I : Y.IdealSheafData}
    {hI : EffectiveCartier I}
    {e : (pullback f).obj (divisorLineBundle I hI) ≅
      divisorLineBundle ⊤ effectiveCartier_top}
    (he : DivisorLineSectionCompatible f hI effectiveCartier_top e) :
    (pullback f).map (divisorSectionMap hI) ≫ e.hom ≫
      (divisorLineBundleTopIso effectiveCartier_top).hom = (modulePullbackUnitIso f).hom := by
  rw [← Category.assoc, he.section, Category.assoc, divisorSection_top_map,
    Iso.inv_hom_id, Category.comp_id]

end FLT.Mazur.FCurve

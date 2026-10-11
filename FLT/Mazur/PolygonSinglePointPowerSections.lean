/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSinglePointPowerNormalization

/-!
# Canonical sections on every single-point normalization power

The marked component comparison preserves the canonical section of O(mP).
On each remaining component the actual original section is the unit in the
specified trivialization. These identities fix the endpoint frames for gluing.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonSinglePointLineNormalization

open FCurve PolygonPinching PolygonMarkedSections PolygonDivisorNormalizationPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Transport the section equation through a specified equality without expanding its geometry. -/
theorem comparison_section_of_eq {X Y : Scheme} (f : X ⟶ Y)
    {I : Y.IdealSheafData} {J : X.IdealSheafData}
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J) (he : I.comap f = J)
    [IsIso (idealModulePullbackHom I f)]
    (e : (Scheme.Modules.pullback f).obj (divisorLineBundle I hI) ≅ divisorLineBundle J hJ)
    (he' : e = divisorLinePullbackIsoOfEq f hI hJ he) :
    (Scheme.Modules.pullback f).map (divisorSectionMap hI) ≫ e.hom =
      (modulePullbackUnitIso f).hom ≫ divisorSectionMap hJ := by
  rw [he']
  exact divisorLinePullbackIsoOfEq_section f hI hJ he

variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The marked component retains the actual canonical section of every original power. -/
@[reassoc] theorem ownComponentPowerIso_section (a : Kˣ) (j : Fin n) (m : ℕ) :
    (Scheme.Modules.pullback (componentι K n j ≫ p).left).map
        (divisorSectionMap ((section_cartier K n p hn q h a j).1.pow m)) ≫
      (ownComponentPowerIso K n hn p q h a j m).hom =
        (modulePullbackUnitIso (componentι K n j ≫ p).left).hom ≫
          divisorSectionMap ((ProjectiveLineMarkedCharts.relativeCartier K a).1.pow m) := by
  let _ := pointPowerIdealComparison_isIso K n hn p q h a j j m
  exact comparison_section_of_eq _ ((section_cartier K n p hn q h a j).1.pow m)
    ((ProjectiveLineMarkedCharts.relativeCartier K a).1.pow m)
    (by rw [idealSheaf_comap_pow, section_ideal K n hn p q h a j])
    (ownComponentPowerIso K n hn p q h a j m) (ownComponentPowerIso_def K n hn p q h a j m)

/-- On every other component the full power section becomes the unit section map. -/
@[reassoc] theorem otherComponentPowerIso_section
    (a : Kˣ) {i j : Fin n} (hij : i ≠ j) (m : ℕ) :
    (Scheme.Modules.pullback (componentι K n i ≫ p).left).map
        (divisorSectionMap ((section_cartier K n p hn q h a j).1.pow m)) ≫
      (otherComponentPowerIso K n hn p q h a hij m).hom =
        (modulePullbackUnitIso (componentι K n i ≫ p).left).hom := by
  let _ := pointPowerIdealComparison_isIso K n hn p q h a i j m
  rw [otherComponentPowerIso_def]
  change _ ≫ (divisorLinePullbackIsoOfEq _ _ _ _).hom ≫
    (divisorLineBundleTopIso effectiveCartier_top).hom = _
  rw [← Category.assoc, divisorLinePullbackIsoOfEq_section, Category.assoc,
    divisorSection_top_map, Iso.inv_hom_id, Category.comp_id]

end FLT.Mazur.PolygonSinglePointLineNormalization

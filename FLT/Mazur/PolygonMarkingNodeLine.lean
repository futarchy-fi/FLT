/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSinglePointLineNormalization
public import FLT.Mazur.DivisorLineSectionCompatibility

/-!
# Canonical marking-line frames at every original polygon node

The marked Cartier ideal restricts to the unit ideal at every node. The
canonical line comparison therefore supplies an actual trivialization that
sends the original vanishing section to one, without choosing a node basis.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkedSections
open PolygonPinching PolygonSinglePointLineNormalization FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLinePullbackIsoOfEq
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

include h in
/-- No original node lies in the scheme-theoretic support of a smooth marking. -/
theorem node_section_ideal (a : Kˣ) (j i : Fin n) :
    (sectionMap K n p a j).ker.comap (nodeι K n i ≫ q).left = ⊤ := by
  let _ := PolygonSeparated.cocone K n hn p q h
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_comap]
  ext x
  change (nodeι K n i ≫ q).left x ∈ (sectionMap K n p a j).ker.support ↔ False
  rw [← SetLike.mem_coe, support_section_ker C.hom _ (section_base K n p a j)]
  constructor
  · rintro ⟨z, hz⟩
    exact PolygonNormalizationTorusPullback.node_not_torus K n hn p q h j i x
      (hz ▸ section_mem_torus K n p a j z)
  · exact False.elim

include h in
/-- Pullback to a node preserves the original marking ideal module. -/
theorem nodeIdealComparison_isIso (a : Kˣ) (j i : Fin n) :
    IsIso (idealModulePullbackHom (sectionMap K n p a j).ker
      (nodeι K n i ≫ q).left) := by
  apply idealModulePullbackHom_isIso_of_cartier _ (section_cartier K n p hn q h a j).1
  rw [node_section_ideal K n hn p q h a j i]
  exact effectiveCartier_top

/-- The canonical comparison with the empty divisor line on an original node. -/
irreducible_def nodeLineIso (a : Kˣ) (j i : Fin n) :
    (Scheme.Modules.pullback (nodeι K n i ≫ q).left).obj (pointLine K n hn p q h a j) ≅
      divisorLineBundle ⊤ effectiveCartier_top := by
  let _ := nodeIdealComparison_isIso K n hn p q h a j i
  exact divisorLinePullbackIsoOfEq _ (section_cartier K n p hn q h a j).1
    effectiveCartier_top (node_section_ideal K n hn p q h a j i)

/-- The canonical node comparison preserves the actual divisor section. -/
theorem nodeLineIso_section (a : Kˣ) (j i : Fin n) :
    DivisorLineSectionCompatible (nodeι K n i ≫ q).left
      (section_cartier K n p hn q h a j).1 effectiveCartier_top
      (nodeLineIso K n hn p q h a j i) := by
  let _ := nodeIdealComparison_isIso K n hn p q h a j i
  rw [nodeLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- The original node frame takes the canonical marking section to the unit section. -/
@[reassoc] theorem nodeLineIso_unit (a : Kˣ) (j i : Fin n) :
    (Scheme.Modules.pullback (nodeι K n i ≫ q).left).map
        (divisorSectionMap (section_cartier K n p hn q h a j).1) ≫
      (nodeLineIso K n hn p q h a j i).hom ≫
        (divisorLineBundleTopIso effectiveCartier_top).hom =
          (modulePullbackUnitIso (nodeι K n i ≫ q).left).hom := by
  rw [← Category.assoc, (nodeLineIso_section K n hn p q h a j i).section,
    Category.assoc, divisorSection_top_map, Iso.inv_hom_id, Category.comp_id]

end FLT.Mazur.PolygonMarkedSections

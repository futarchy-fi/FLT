/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMarkingBaseChange
public import FLT.Mazur.PolygonMarkingNodeLine
public import FLT.Mazur.RelativeCartierMorphismBaseChange
public import FLT.Mazur.DivisorEmptyLinePullback

/-!
# Original node frames under arbitrary base change

Every original node stays outside the actual family marking divisor. Its
canonical line frame retains the unit section and the base-change square.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkingBaseChange
open PolygonPinching PolygonMarkedSections FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLinePullbackIsoOfEq
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  {T : Scheme} (g : T ⟶ Spec (.of K)) (a : Kˣ) (j i : Fin n)

include h in
/-- At an original base-changed node the full marking ideal is the unit ideal. -/
theorem node_ideal :
    (markingIdeal K n p g a j).comap ((Over.pullback g).map (nodeι K n i ≫ q)).left = ⊤ := by
  have he := relativeCartierMorphismBaseChange_ideal (nodeι K n i ≫ q) g _ _
    (node_section_ideal K n hn p q h a j i)
  exact he.trans (Scheme.IdealSheafData.comap_top _)

/-- The actual family node comparison with the canonical empty-divisor line. -/
irreducible_def nodeLineIso :
    (Scheme.Modules.pullback ((Over.pullback g).map (nodeι K n i ≫ q)).left).obj
      (markingLine K n hn p q h g a j) ≅ divisorLineBundle ⊤ effectiveCartier_top := by
  let hs := (markingIdeal_cartier K n hn p q h g a j).1
  let he := node_ideal K n hn p q h g a j i
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ effectiveCartier_top)
  exact divisorLinePullbackIsoOfEq _ hs effectiveCartier_top he

/-- The original node comparison preserves the actual family marking section. -/
theorem nodeLineIso_section :
    DivisorLineSectionCompatible ((Over.pullback g).map (nodeι K n i ≫ q)).left
      (markingIdeal_cartier K n hn p q h g a j).1 effectiveCartier_top
      (nodeLineIso K n hn p q h g a j i) := by
  let hs := (markingIdeal_cartier K n hn p q h g a j).1
  let he := node_ideal K n hn p q h g a j i
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ effectiveCartier_top)
  rw [nodeLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- Node restriction and base change commute on the actual line, including its unit frame. -/
theorem nodeLineIso_square :
    LinePullbackSquare ((Over.pullback g).map (nodeι K n i ≫ q)).left
      (pullback.fst C.hom g) (pullback.fst (point K).hom g) (nodeι K n i ≫ q).left
      (OverPullbackLocalPushout.map_isPullback g (nodeι K n i ≫ q)).w
      (markingLineIso K n hn p q h g a j) (nodeLineIso K n hn p q h g a j i)
      (PolygonMarkedSections.nodeLineIso K n hn p q h a j i)
      (divisorEmptyLinePullbackIso (pullback.fst (point K).hom g)) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (markingLineIso_section K n hn p q h g a j)
    (nodeLineIso_section K n hn p q h g a j i)
    (PolygonMarkedSections.nodeLineIso_section K n hn p q h a j i)
    (divisorEmptyLinePullbackIso_section _)

/-- The original family node frame takes the canonical marking section to one. -/
@[reassoc] theorem nodeLineIso_unit :
    (Scheme.Modules.pullback ((Over.pullback g).map (nodeι K n i ≫ q)).left).map
        (divisorSectionMap (markingIdeal_cartier K n hn p q h g a j).1) ≫
      (nodeLineIso K n hn p q h g a j i).hom ≫
        (divisorLineBundleTopIso effectiveCartier_top).hom =
          (modulePullbackUnitIso ((Over.pullback g).map (nodeι K n i ≫ q)).left).hom :=
  (nodeLineIso_section K n hn p q h g a j i).unit _

end FLT.Mazur.PolygonMarkingBaseChange

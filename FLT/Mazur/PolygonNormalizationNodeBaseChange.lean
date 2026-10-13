/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNormalizationBaseChangeLine
public import FLT.Mazur.PolygonNodeBaseChangeLine
public import FLT.Mazur.PolygonNormalizationNodeLine

/-!
# Both original normalization branches retain the family node frame

The endpoint comparisons on the original base-changed normalization agree with
the original base-changed node comparison. The actual line triangle retains
both incidence maps and propagates to every tensor degree.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkingBaseChange
open PolygonPinching PolygonMarkedSections FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLinePullbackIsoOfEq tensorPowerPullbackComparison
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  {T : Scheme} (g : T ⟶ Spec (.of K)) (a : Kˣ) (j i k : Fin n)
  (s : point K ⟶ component K) (w : s ≫ (componentι K n i ≫ p) = nodeι K n k ≫ q)

omit [NeZero n] in
include w in
/-- The original branch incidence remains an equality after arbitrary base change. -/
theorem normalizationNode_baseChange_left :
    ((Over.pullback g).map s).left ≫ ((Over.pullback g).map (componentι K n i ≫ p)).left =
      ((Over.pullback g).map (nodeι K n k ≫ q)).left := by
  rw [← Over.comp_left, ← Functor.map_comp, w]

include h w in
/-- Either original family endpoint sees the full normalization marking ideal as the unit ideal. -/
theorem normalizationEndpoint_baseChange_ideal :
    (((sectionMap K n p a j).ker.comap (componentι K n i ≫ p).left).comap
      (pullback.fst (component K).hom g)).comap ((Over.pullback g).map s).left = ⊤ := by
  have he := relativeCartierMorphismBaseChange_ideal s g _ _
    (PolygonSinglePointLineNormalization.normalizationEndpointIdeal_eq
      K n hn p q h a j i k s w)
  exact he.trans (Scheme.IdealSheafData.comap_top _)

/-- Canonical endpoint comparison on the actual base-changed normalization. -/
irreducible_def normalizationEndpointLineIso :
    (Scheme.Modules.pullback ((Over.pullback g).map s).left).obj
      (normalizationMarkingLine K n hn p q h a j i g) ≅
        divisorLineBundle ⊤ effectiveCartier_top := by
  let hs := (relativeCartierBaseChange (component K).hom g _
    (normalizationIdeal_relativeCartier K n hn p q h a j i)).1
  let he := normalizationEndpoint_baseChange_ideal K n hn p q h g a j i k s w
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ effectiveCartier_top)
  exact divisorLinePullbackIsoOfEq _ hs effectiveCartier_top he

/-- The original family endpoint comparison preserves the canonical marking section. -/
theorem normalizationEndpointLineIso_section :
    DivisorLineSectionCompatible ((Over.pullback g).map s).left
      (relativeCartierBaseChange (component K).hom g _
        (normalizationIdeal_relativeCartier K n hn p q h a j i)).1 effectiveCartier_top
      (normalizationEndpointLineIso K n hn p q h g a j i k s w) := by
  let hs := (relativeCartierBaseChange (component K).hom g _
    (normalizationIdeal_relativeCartier K n hn p q h a j i)).1
  let he := normalizationEndpoint_baseChange_ideal K n hn p q h g a j i k s w
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ effectiveCartier_top)
  rw [normalizationEndpointLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- Normalization and endpoint restriction recover the actual family node comparison. -/
theorem normalizationLineIso_node :
    LinePullbackTriangle ((Over.pullback g).map s).left
      ((Over.pullback g).map (componentι K n i ≫ p)).left
      ((Over.pullback g).map (nodeι K n k ≫ q)).left
      (normalizationNode_baseChange_left K n p q g i k s w)
      (normalizationLineIso K n hn p q h a j i g)
      (normalizationEndpointLineIso K n hn p q h g a j i k s w)
      (nodeLineIso K n hn p q h g a j k) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (normalizationLineIso_section K n hn p q h a j i g)
    (normalizationEndpointLineIso_section K n hn p q h g a j i k s w)
    (nodeLineIso_section K n hn p q h g a j k)

/-- The same original incidence triangle holds in every tensor degree, including zero. -/
theorem normalizationLineIso_node_power (d : ℕ) :
    LinePullbackTriangle ((Over.pullback g).map s).left
      ((Over.pullback g).map (componentι K n i ≫ p)).left
      ((Over.pullback g).map (nodeι K n k ≫ q)).left
      (normalizationNode_baseChange_left K n p q g i k s w)
      (tensorPowerPullbackComparison _ (normalizationLineIso K n hn p q h a j i g) d)
      (tensorPowerPullbackComparison _
        (normalizationEndpointLineIso K n hn p q h g a j i k s w) d)
      (tensorPowerPullbackComparison _ (nodeLineIso K n hn p q h g a j k) d) :=
  (normalizationLineIso_node K n hn p q h g a j i k s w).tensorPower d

end FLT.Mazur.PolygonMarkingBaseChange

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMarkingNormalizationLine
public import FLT.Mazur.PolygonMarkingNodeLine
public import FLT.Mazur.DivisorLineSectionTriangle

/-!
# The two normalization branches retain the original node frame

Every component endpoint comparison agrees with the canonical line comparison
at its original polygon node. The zero and infinity branches therefore use the
same original frame, including for the one-gon and in every tensor degree.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonSinglePointLineNormalization
open PolygonPinching PolygonMarkedSections FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLinePullbackIsoOfEq tensorPowerPullbackComparison
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Kˣ) (j i k : Fin n) (s : point K ⟶ component K)
  (w : s ≫ (componentι K n i ≫ p) = nodeι K n k ≫ q)

include h w in
/-- The actual pulled marking ideal is the unit ideal at either original component endpoint. -/
theorem normalizationEndpointIdeal_eq :
    ((sectionMap K n p a j).ker.comap (componentι K n i ≫ p).left).comap s.left = ⊤ := by
  rw [← Scheme.IdealSheafData.comap_comp]
  have hw := congrArg Over.Hom.left w
  change s.left ≫ (componentι K n i ≫ p).left = (nodeι K n k ≫ q).left at hw
  rw [hw, node_section_ideal K n hn p q h a j k]

/-- The actual endpoint comparison into the canonical empty-divisor line at the node. -/
irreducible_def normalizationEndpointLineIso :
    (Scheme.Modules.pullback s.left).obj
      (divisorLineBundle _ (normalizationIdeal_cartier K n hn p q h a j i)) ≅
        divisorLineBundle ⊤ effectiveCartier_top := by
  let ht := normalizationIdeal_cartier K n hn p q h a j i
  let hw := normalizationEndpointIdeal_eq K n hn p q h a j i k s w
  let _ := idealModulePullbackHom_isIso_of_cartier s.left ht
    (hw.symm ▸ effectiveCartier_top)
  exact divisorLinePullbackIsoOfEq _ ht effectiveCartier_top hw

/-- The endpoint comparison retains the original canonical section. -/
theorem normalizationEndpointLineIso_section :
    DivisorLineSectionCompatible s.left
      (normalizationIdeal_cartier K n hn p q h a j i) effectiveCartier_top
      (normalizationEndpointLineIso K n hn p q h a j i k s w) := by
  let ht := normalizationIdeal_cartier K n hn p q h a j i
  let hw := normalizationEndpointIdeal_eq K n hn p q h a j i k s w
  let _ := idealModulePullbackHom_isIso_of_cartier s.left ht
    (hw.symm ▸ effectiveCartier_top)
  rw [normalizationEndpointLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- Component restriction followed by endpoint restriction is the original node comparison. -/
theorem normalizationLineIso_node :
    LinePullbackTriangle s.left (componentι K n i ≫ p).left (nodeι K n k ≫ q).left
      (congrArg Over.Hom.left w) (normalizationLineIso K n hn p q h a j i)
      (normalizationEndpointLineIso K n hn p q h a j i k s w)
      (nodeLineIso K n hn p q h a j k) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (normalizationLineIso_section K n hn p q h a j i)
    (normalizationEndpointLineIso_section K n hn p q h a j i k s w)
    (nodeLineIso_section K n hn p q h a j k)

/-- Every tensor degree retains the original normalization-to-node comparison. -/
theorem normalizationLineIso_node_power (d : ℕ) :
    LinePullbackTriangle s.left (componentι K n i ≫ p).left (nodeι K n k ≫ q).left
      (congrArg Over.Hom.left w)
      (tensorPowerPullbackComparison _ (normalizationLineIso K n hn p q h a j i) d)
      (tensorPowerPullbackComparison _
        (normalizationEndpointLineIso K n hn p q h a j i k s w) d)
      (tensorPowerPullbackComparison _ (nodeLineIso K n hn p q h a j k) d) :=
  (normalizationLineIso_node K n hn p q h a j i k s w).tensorPower d

/-- The zero branch at an original node uses that node's original marking-line frame. -/
theorem normalizationLineIso_zero_node (d : ℕ) :
    LinePullbackTriangle (ProjectiveLine.zeroSection K).left
      (componentι K n i ≫ p).left (nodeι K n i ≫ q).left
      (congrArg Over.Hom.left (PolygonNodeIncidence.zero_node K n hn p q h i))
      (tensorPowerPullbackComparison _ (normalizationLineIso K n hn p q h a j i) d)
      (tensorPowerPullbackComparison _
        (normalizationEndpointLineIso K n hn p q h a j i i (ProjectiveLine.zeroSection K)
          (PolygonNodeIncidence.zero_node K n hn p q h i)) d)
      (tensorPowerPullbackComparison _ (nodeLineIso K n hn p q h a j i) d) :=
  normalizationLineIso_node_power K n hn p q h a j i i (ProjectiveLine.zeroSection K)
    (PolygonNodeIncidence.zero_node K n hn p q h i) d

/-- The adjacent infinity branch uses the very same original node frame in every degree. -/
theorem normalizationLineIso_infinity_node (d : ℕ) :
    LinePullbackTriangle (ProjectiveLine.infinitySection K).left
      (componentι K n (next hn i) ≫ p).left (nodeι K n i ≫ q).left
      (congrArg Over.Hom.left (PolygonNodeIncidence.infinity_node K n hn p q h i))
      (tensorPowerPullbackComparison _
        (normalizationLineIso K n hn p q h a j (next hn i)) d)
      (tensorPowerPullbackComparison _
        (normalizationEndpointLineIso K n hn p q h a j (next hn i) i
          (ProjectiveLine.infinitySection K)
          (PolygonNodeIncidence.infinity_node K n hn p q h i)) d)
      (tensorPowerPullbackComparison _ (nodeLineIso K n hn p q h a j i) d) :=
  normalizationLineIso_node_power K n hn p q h a j (next hn i) i
    (ProjectiveLine.infinitySection K) (PolygonNodeIncidence.infinity_node K n hn p q h i) d

end FLT.Mazur.PolygonSinglePointLineNormalization

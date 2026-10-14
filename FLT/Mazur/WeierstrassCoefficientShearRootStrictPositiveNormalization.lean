/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootStrictPositiveCycle
public import FLT.Mazur.WeierstrassDividedPositiveSplitCocone

/-!
# Complete normalization and node comparison in the coefficient model

The independent full branch cycle and the unchanged exterior form the original
pinching diagram. Reconstruction preserves both entire coproduct maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "p" => coefficientShearGluedStructure hπ data K 0 (s + 1) hs
local notation "E" => coefficientShearGluedOverIso hπ data K 0 (s + 1) hs

/-- The normalization leg is the coproduct of the complete actual projective components. -/
def coefficientShearRootStrictPositiveNormalization :
    PolygonPinching.components K (2 * s + 5) ⟶ Over.mk p :=
  Sigma.desc (coefficientShearRootStrictPositiveCycleComponent hπ data D s hs hstart hk hp)

/-- Each normalization summand keeps its entire original component parameterization. -/
@[reassoc] theorem coefficientShearRootStrictPositiveNormalization_ι (i : Fin (2 * s + 5)) :
    PolygonPinching.componentι K (2 * s + 5) i ≫
        coefficientShearRootStrictPositiveNormalization hπ data D s hs hstart hk hp =
      coefficientShearRootStrictPositiveCycleComponent hπ data D s hs hstart hk hp i :=
  Sigma.ι_comp_desc _ _

/-- The node leg consists of the original sections in the proved cyclic order. -/
def coefficientShearRootStrictPositiveNodes : PolygonPinching.nodes K (2 * s + 5) ⟶ Over.mk p :=
  Sigma.desc (fun i => finalNodeOverSection hπ data D s hs hk hp
    (positiveSplitCycleNodeIndex start s hstart i) ≫ (E).inv)

/-- Every node summand retains the whole original section over the field. -/
@[reassoc] theorem coefficientShearRootStrictPositiveNodes_ι (i : Fin (2 * s + 5)) :
    PolygonPinching.nodeι K (2 * s + 5) i ≫
        coefficientShearRootStrictPositiveNodes hπ data D s hs hstart hk hp =
      finalNodeOverSection hπ data D s hs hk hp
        (positiveSplitCycleNodeIndex start s hstart i) ≫ (E).inv :=
  Sigma.ι_comp_desc _ _

/-- The specified polygon pinching diagram commutes for these actual component and node legs. -/
theorem coefficientShearRootStrictPositiveCocone_condition :
    PolygonPinching.toComponents K (2 * s + 5) (by omega) ≫
        coefficientShearRootStrictPositiveNormalization hπ data D s hs hstart hk hp =
      PolygonPinching.toNodes K (2 * s + 5) ≫
        coefficientShearRootStrictPositiveNodes hπ data D s hs hstart hk hp := by
  apply Sigma.hom_ext
  rintro ⟨i, b⟩
  change PolygonPinching.branchι K (2 * s + 5) i b ≫ _ =
    PolygonPinching.branchι K (2 * s + 5) i b ≫ _
  cases b
  · rw [PolygonPinching.branchι_toComponents_zero_assoc,
      coefficientShearRootStrictPositiveNormalization_ι,
      coefficientShearRootStrictPositiveCycleComponent_zero,
      PolygonPinching.branchι_toNodes_assoc, coefficientShearRootStrictPositiveNodes_ι]
  · rw [PolygonPinching.branchι_toComponents_infinity_assoc,
      coefficientShearRootStrictPositiveNormalization_ι,
      coefficientShearRootStrictPositiveCycleComponent_next_infinity,
      PolygonPinching.branchι_toNodes_assoc, coefficientShearRootStrictPositiveNodes_ι]

/-- A constructed pushout cocone, without an assumed universal property. -/
def coefficientShearRootStrictPositiveCocone :
    PushoutCocone (PolygonPinching.toComponents K (2 * s + 5) (by omega))
      (PolygonPinching.toNodes K (2 * s + 5)) :=
  PushoutCocone.mk (coefficientShearRootStrictPositiveNormalization hπ data D s hs hstart hk hp)
    (coefficientShearRootStrictPositiveNodes hπ data D s hs hstart hk hp)
    (coefficientShearRootStrictPositiveCocone_condition hπ data D s hs hstart hk hp)

/-- The full independent normalization reconstructs the entire original normalization map. -/
@[reassoc] theorem coefficientShearRootStrictPositiveNormalization_original :
    coefficientShearRootStrictPositiveNormalization hπ data D s hs hstart hk hp ≫ (E).hom =
      positiveSplitCycleNormalization hπ data D s hs hstart hk hp := by
  apply Sigma.hom_ext
  intro i
  change PolygonPinching.componentι K (2 * s + 5) i ≫ _ =
    PolygonPinching.componentι K (2 * s + 5) i ≫ _
  rw [coefficientShearRootStrictPositiveNormalization_ι_assoc,
    coefficientShearRootStrictPositiveCycleComponent_original, positiveSplitCycleNormalization_ι]

/-- The whole node coproduct reconstructs the original without reindexing any node. -/
@[reassoc] theorem coefficientShearRootStrictPositiveNodes_original :
    coefficientShearRootStrictPositiveNodes hπ data D s hs hstart hk hp ≫ (E).hom =
      positiveSplitCycleNodes hπ data D s hs hstart hk hp := by
  apply Sigma.hom_ext
  intro i
  change PolygonPinching.nodeι K (2 * s + 5) i ≫ _ =
    PolygonPinching.nodeι K (2 * s + 5) i ≫ _
  rw [coefficientShearRootStrictPositiveNodes_ι_assoc,
    Iso.inv_hom_id, Category.comp_id, positiveSplitCycleNodes_ι]

/-- Distinct cyclic positions remain distinct complete component maps in the coefficient model. -/
theorem coefficientShearRootStrictPositiveCycleComponent_index_injective :
    Function.Injective
      (coefficientShearRootStrictPositiveCycleComponent hπ data D s hs hstart hk hp) := by
  intro i j he
  apply positiveSplitCycleComponent_index_injective hπ data D s hs hstart hk hp
  simpa only [coefficientShearRootStrictPositiveCycleComponent_original] using
    congrArg (fun f => f ≫ (E).hom) he

end FLT.Mazur.WeierstrassDividedDepth

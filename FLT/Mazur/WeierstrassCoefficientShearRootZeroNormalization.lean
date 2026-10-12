/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootZeroCycle
public import FLT.Mazur.WeierstrassDividedZeroSplitCocone

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
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "p" => coefficientShearGluedStructure hπ data K 0 (s + 1) hs
local notation "E" => coefficientShearGluedOverIso hπ data K 0 (s + 1) hs

/-- The normalization leg is the coproduct of the complete actual projective components. -/
def coefficientShearRootZeroNormalization : PolygonPinching.components K (2 * s + 3) ⟶ Over.mk p :=
  Sigma.desc (coefficientShearRootZeroCycleComponent hπ data D s hs hstart hk hp)

/-- Each normalization summand keeps its entire original component parameterization. -/
@[reassoc] theorem coefficientShearRootZeroNormalization_ι (i : Fin (2 * s + 3)) :
    PolygonPinching.componentι K (2 * s + 3) i ≫
        coefficientShearRootZeroNormalization hπ data D s hs hstart hk hp =
      coefficientShearRootZeroCycleComponent hπ data D s hs hstart hk hp i :=
  Sigma.ι_comp_desc _ _

/-- The node leg consists of the original sections in the proved cyclic order. -/
def coefficientShearRootZeroNodes : PolygonPinching.nodes K (2 * s + 3) ⟶ Over.mk p :=
  Sigma.desc (fun i => coefficientShearFinalNodeOverSection hπ data D s hs hk hp
    (zeroSplitCycleNodeIndex start s i))

/-- Every node summand retains the whole original section over the field. -/
@[reassoc] theorem coefficientShearRootZeroNodes_ι (i : Fin (2 * s + 3)) :
    PolygonPinching.nodeι K (2 * s + 3) i ≫
        coefficientShearRootZeroNodes hπ data D s hs hk hp =
      coefficientShearFinalNodeOverSection hπ data D s hs hk hp
        (zeroSplitCycleNodeIndex start s i) :=
  Sigma.ι_comp_desc _ _

/-- The specified polygon pinching diagram commutes for these actual component and node legs. -/
theorem coefficientShearRootZeroCocone_condition :
    PolygonPinching.toComponents K (2 * s + 3) (by omega) ≫
        coefficientShearRootZeroNormalization hπ data D s hs hstart hk hp =
      PolygonPinching.toNodes K (2 * s + 3) ≫
        coefficientShearRootZeroNodes hπ data D s hs hk hp := by
  apply Sigma.hom_ext
  rintro ⟨i, b⟩
  change PolygonPinching.branchι K (2 * s + 3) i b ≫ _ =
    PolygonPinching.branchι K (2 * s + 3) i b ≫ _
  cases b
  · rw [PolygonPinching.branchι_toComponents_zero_assoc,
      coefficientShearRootZeroNormalization_ι, coefficientShearRootZeroCycleComponent_zero,
      PolygonPinching.branchι_toNodes_assoc, coefficientShearRootZeroNodes_ι]
  · rw [PolygonPinching.branchι_toComponents_infinity_assoc,
      coefficientShearRootZeroNormalization_ι, coefficientShearRootZeroCycleComponent_next_infinity,
      PolygonPinching.branchι_toNodes_assoc, coefficientShearRootZeroNodes_ι]

/-- A constructed pushout cocone, without an assumed universal property. -/
def coefficientShearRootZeroCocone :
    PushoutCocone (PolygonPinching.toComponents K (2 * s + 3) (by omega))
      (PolygonPinching.toNodes K (2 * s + 3)) :=
  PushoutCocone.mk (coefficientShearRootZeroNormalization hπ data D s hs hstart hk hp)
    (coefficientShearRootZeroNodes hπ data D s hs hk hp)
    (coefficientShearRootZeroCocone_condition hπ data D s hs hstart hk hp)

/-- The full independent normalization reconstructs the entire original normalization map. -/
@[reassoc] theorem coefficientShearRootZeroNormalization_original :
    coefficientShearRootZeroNormalization hπ data D s hs hstart hk hp ≫ (E).hom =
      zeroSplitCycleNormalization hπ data D s hs hstart hk hp := by
  apply Sigma.hom_ext
  intro i
  change PolygonPinching.componentι K (2 * s + 3) i ≫ _ =
    PolygonPinching.componentι K (2 * s + 3) i ≫ _
  rw [coefficientShearRootZeroNormalization_ι_assoc,
    coefficientShearRootZeroCycleComponent_original, zeroSplitCycleNormalization_ι]

/-- The whole node coproduct reconstructs the original without reindexing any node. -/
@[reassoc] theorem coefficientShearRootZeroNodes_original :
    coefficientShearRootZeroNodes hπ data D s hs hk hp ≫ (E).hom =
      zeroSplitCycleNodes hπ data D s hs hk hp := by
  apply Sigma.hom_ext
  intro i
  change PolygonPinching.nodeι K (2 * s + 3) i ≫ _ =
    PolygonPinching.nodeι K (2 * s + 3) i ≫ _
  rw [coefficientShearRootZeroNodes_ι_assoc,
    coefficientShearFinalNodeOverSection_original, zeroSplitCycleNodes_ι]

/-- Distinct cyclic positions remain distinct complete component maps in the coefficient model. -/
theorem coefficientShearRootZeroCycleComponent_index_injective :
    Function.Injective (coefficientShearRootZeroCycleComponent hπ data D s hs hstart hk hp) := by
  intro i j he
  apply zeroSplitCycleComponent_index_injective hπ data D s hs hstart hk hp
  simpa only [coefficientShearRootZeroCycleComponent_original] using
    congrArg (fun f => f ≫ (E).hom) he

end FLT.Mazur.WeierstrassDividedDepth

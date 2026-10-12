/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootPositiveCycle
public import FLT.Mazur.WeierstrassDividedPositiveEqualityCocone

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
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "p" => coefficientShearGluedStructure hπ data K 0 (s + 1) hs
local notation "E" => coefficientShearGluedOverIso hπ data K 0 (s + 1) hs

/-- The normalization leg is the coproduct of the complete actual projective components. -/
def coefficientShearRootPositiveNormalization :
    PolygonPinching.components K (2 * s + 4) ⟶ Over.mk p :=
  Sigma.desc (coefficientShearRootPositiveCycleComponent hπ data D s hs hstart hk hp)

/-- Each normalization summand keeps its entire original component parameterization. -/
@[reassoc] theorem coefficientShearRootPositiveNormalization_ι (i : Fin (2 * s + 4)) :
    PolygonPinching.componentι K (2 * s + 4) i ≫
        coefficientShearRootPositiveNormalization hπ data D s hs hstart hk hp =
      coefficientShearRootPositiveCycleComponent hπ data D s hs hstart hk hp i :=
  Sigma.ι_comp_desc _ _

/-- The node leg consists of the original sections in the proved cyclic order. -/
def coefficientShearRootPositiveNodes : PolygonPinching.nodes K (2 * s + 4) ⟶ Over.mk p :=
  Sigma.desc (fun i => equalityNodeOverSection hπ data D s hs hk
    (positiveEqualityCycleNodeIndex start s hstart i) ≫ (E).inv)

/-- Every node summand retains the whole original section over the field. -/
@[reassoc] theorem coefficientShearRootPositiveNodes_ι (i : Fin (2 * s + 4)) :
    PolygonPinching.nodeι K (2 * s + 4) i ≫
        coefficientShearRootPositiveNodes hπ data D s hs hstart hk =
      equalityNodeOverSection hπ data D s hs hk
        (positiveEqualityCycleNodeIndex start s hstart i) ≫ (E).inv :=
  Sigma.ι_comp_desc _ _

/-- The specified polygon pinching diagram commutes for these actual component and node legs. -/
theorem coefficientShearRootPositiveCocone_condition :
    PolygonPinching.toComponents K (2 * s + 4) (by omega) ≫
        coefficientShearRootPositiveNormalization hπ data D s hs hstart hk hp =
      PolygonPinching.toNodes K (2 * s + 4) ≫
        coefficientShearRootPositiveNodes hπ data D s hs hstart hk := by
  apply Sigma.hom_ext
  rintro ⟨i, b⟩
  change PolygonPinching.branchι K (2 * s + 4) i b ≫ _ =
    PolygonPinching.branchι K (2 * s + 4) i b ≫ _
  cases b
  · rw [PolygonPinching.branchι_toComponents_zero_assoc,
      coefficientShearRootPositiveNormalization_ι, coefficientShearRootPositiveCycleComponent_zero,
      PolygonPinching.branchι_toNodes_assoc, coefficientShearRootPositiveNodes_ι]
  · rw [PolygonPinching.branchι_toComponents_infinity_assoc,
      coefficientShearRootPositiveNormalization_ι,
      coefficientShearRootPositiveCycleComponent_next_infinity,
      PolygonPinching.branchι_toNodes_assoc, coefficientShearRootPositiveNodes_ι]

/-- A constructed pushout cocone, without an assumed universal property. -/
def coefficientShearRootPositiveCocone :
    PushoutCocone (PolygonPinching.toComponents K (2 * s + 4) (by omega))
      (PolygonPinching.toNodes K (2 * s + 4)) :=
  PushoutCocone.mk (coefficientShearRootPositiveNormalization hπ data D s hs hstart hk hp)
    (coefficientShearRootPositiveNodes hπ data D s hs hstart hk)
    (coefficientShearRootPositiveCocone_condition hπ data D s hs hstart hk hp)

/-- The full independent normalization reconstructs the entire original normalization map. -/
@[reassoc] theorem coefficientShearRootPositiveNormalization_original :
    coefficientShearRootPositiveNormalization hπ data D s hs hstart hk hp ≫ (E).hom =
      positiveEqualityCycleNormalization hπ data D s hs hstart hk hp := by
  apply Sigma.hom_ext
  intro i
  change PolygonPinching.componentι K (2 * s + 4) i ≫ _ =
    PolygonPinching.componentι K (2 * s + 4) i ≫ _
  rw [coefficientShearRootPositiveNormalization_ι_assoc,
    coefficientShearRootPositiveCycleComponent_original, positiveEqualityCycleNormalization_ι]

/-- The whole node coproduct reconstructs the original without reindexing any node. -/
@[reassoc] theorem coefficientShearRootPositiveNodes_original :
    coefficientShearRootPositiveNodes hπ data D s hs hstart hk ≫ (E).hom =
      positiveEqualityCycleNodes hπ data D s hs hstart hk := by
  apply Sigma.hom_ext
  intro i
  change PolygonPinching.nodeι K (2 * s + 4) i ≫ _ =
    PolygonPinching.nodeι K (2 * s + 4) i ≫ _
  rw [coefficientShearRootPositiveNodes_ι_assoc,
    Iso.inv_hom_id, Category.comp_id, positiveEqualityCycleNodes_ι]

/-- Distinct cyclic positions remain distinct complete component maps in the coefficient model. -/
theorem coefficientShearRootPositiveCycleComponent_index_injective :
    Function.Injective
      (coefficientShearRootPositiveCycleComponent hπ data D s hs hstart hk hp) := by
  intro i j he
  apply positiveEqualityCycleComponent_index_injective hπ data D s hs hstart hk hp
  simpa only [coefficientShearRootPositiveCycleComponent_original] using
    congrArg (fun f => f ≫ (E).hom) he

end FLT.Mazur.WeierstrassDividedDepth

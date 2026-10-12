/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootPositivePinching
public import FLT.Mazur.WeierstrassDividedPositiveEqualityReflection
public import FLT.Mazur.NeronPolygonReflection
import all FLT.Mazur.WeierstrassDividedPositiveEqualityPushout

/-!
# Reflection through the independently assembled positive pinching

Descend the reflected full normalization through the coefficient-model pushout.
Reconstruction identifies it with the original indexed reflection on the whole fiber.
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
local notation "Z" => coefficientShearRootPositiveCycleComponent hπ data D s hs hstart hk hp
local notation "N" => coefficientShearRootPositiveNormalization hπ data D s hs hstart hk hp
local notation "Q" => coefficientShearRootPositiveNodes hπ data D s hs hstart hk
local notation "H" => coefficientShearRootPositiveCocone_isPushout hπ data D s hs hstart hk hp
local notation "ρ" => Iso.hom (ProjectiveLine.endpointReversalOverIso K)

/-- Reflection descended through the actual original residue-model pushout. -/
def coefficientShearRootPositiveReflection : Over.mk p ⟶ Over.mk p :=
  PolygonPinching.polygonReflection K (by omega) N Q H
local notation "σ" => coefficientShearRootPositiveReflection hπ data D s hs hstart hk hp

/-- The full normalization is reflected, with no restriction to its smooth locus. -/
@[reassoc] theorem coefficientShearRootPositiveReflection_normalization :
    N ≫ σ = PolygonPinching.componentsReflection K ≫ N :=
  PolygonPinching.components_polygonReflection K (by omega) N Q H

/-- The entire original node coproduct is retained by reflection. -/
@[reassoc] theorem coefficientShearRootPositiveReflection_nodes :
    Q ≫ σ = PolygonPinching.nodesReflection K ≫ Q :=
  PolygonPinching.nodes_polygonReflection K (by omega) N Q H

/-- Every complete component has index minus i and reversed projective coordinate. -/
@[reassoc] theorem coefficientShearRootPositiveReflection_component (i : Fin (2 * s + 4)) :
    Z i ≫ σ = ρ ≫ Z (PolygonPinching.reflectIndex i) := by
  have h := PolygonPinching.componentι_polygonReflection K (by omega) N Q H i
  simpa only [coefficientShearRootPositiveReflection, coefficientShearRootPositiveNormalization_ι,
    coefficientShearRootPositiveNormalization_ι_assoc] using h

/-- Each actual cyclic node has the original minus-one offset under reflection. -/
@[reassoc] theorem coefficientShearRootPositiveReflection_node (i : Fin (2 * s + 4)) :
    (equalityNodeOverSection hπ data D s hs hk
        (positiveEqualityCycleNodeIndex start s hstart i) ≫ (E).inv) ≫ σ =
      equalityNodeOverSection hπ data D s hs hk
        (positiveEqualityCycleNodeIndex start s hstart (PolygonPinching.reflectNodeIndex i)) ≫
          (E).inv := by
  have h := PolygonPinching.nodeι_polygonReflection K (by omega) N Q H i
  simpa only [coefficientShearRootPositiveReflection, coefficientShearRootPositiveNodes_ι,
    coefficientShearRootPositiveNodes_ι_assoc, Category.assoc] using h

/-- Reflection squares to the identity on the whole original model, including its nodes. -/
@[reassoc] theorem coefficientShearRootPositiveReflection_involutive : σ ≫ σ = 𝟙 _ :=
  PolygonPinching.polygonReflection_involutive K (by omega) N Q H

/-- The constructed reflection is an automorphism over the actual residue field. -/
def coefficientShearRootPositiveReflectionIso : Over.mk p ≅ Over.mk p where
  hom := σ
  inv := σ
  hom_inv_id := coefficientShearRootPositiveReflection_involutive hπ data D s hs hstart hk hp
  inv_hom_id := coefficientShearRootPositiveReflection_involutive hπ data D s hs hstart hk hp

/-- Reconstruction intertwines the descended reflection on the entire original residue fiber. -/
@[reassoc] theorem coefficientShearRootPositiveReflection_original :
    σ ≫ (E).hom = (E).hom ≫ positiveEqualityReflection hπ data D s hs hstart hk hp := by
  apply (H).hom_ext
  · rw [← Category.assoc, coefficientShearRootPositiveReflection_normalization,
      Category.assoc, coefficientShearRootPositiveNormalization_original,
      ← Category.assoc, coefficientShearRootPositiveNormalization_original,
      positiveEqualityReflection_normalization]
  · rw [← Category.assoc, coefficientShearRootPositiveReflection_nodes,
      Category.assoc, coefficientShearRootPositiveNodes_original,
      ← Category.assoc, coefficientShearRootPositiveNodes_original,
      positiveEqualityReflection_nodes]

/-- The full independent component formulas uniquely determine reflection, including all nodes. -/
theorem coefficientShearRootPositiveReflection_unique (f : Over.mk p ⟶ Over.mk p)
    (h : ∀ i, Z i ≫ f = ρ ≫ Z (PolygonPinching.reflectIndex i)) : f = σ := by
  let _ := positiveEqualityCycleNormalization_epi hπ data D s hs hstart hk hp
  let _ : Epi N := by
    rw [← epi_comp_iff_of_isIso N (E).hom,
      coefficientShearRootPositiveNormalization_original]
    infer_instance
  apply (cancel_epi N).mp
  apply Sigma.hom_ext
  intro i
  change PolygonPinching.componentι K (2 * s + 4) i ≫ N ≫ f =
    PolygonPinching.componentι K (2 * s + 4) i ≫ N ≫ σ
  rw [coefficientShearRootPositiveNormalization_ι_assoc,
    coefficientShearRootPositiveNormalization_ι_assoc, h i,
    coefficientShearRootPositiveReflection_component]

end FLT.Mazur.WeierstrassDividedDepth

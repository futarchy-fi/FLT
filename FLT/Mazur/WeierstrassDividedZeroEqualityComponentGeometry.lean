/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonProper
public import FLT.Mazur.ProjectiveLineTopology
public import FLT.Mazur.WeierstrassDividedZeroEqualityCycle
public import FLT.Mazur.WeierstrassDividedZeroSplitComponentInjectivity

/-!
# Proper embedded images of the actual equality-depth components

Each complete original component map is proper and injective on points. Its
image is closed and is the closure of its specified dense Laurent coordinate.
These are topological embeddings; no scheme closed immersion is assumed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing TopologicalSpace Topology
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
/-- Endpoint reversal preserves point injectivity over the coefficient field. -/
theorem equalityComponent_reversal_injective {K : Type u} [Field K]
    {X : Over (Spec (.of K))} (f : PolygonPinching.component K ⟶ X)
    (hf : Function.Injective f.left) :
    Function.Injective ((ProjectiveLine.endpointReversalOverIso K).hom ≫ f).left :=
  hf.comp (ProjectiveLine.endpointReversalIso K).hom.homeomorph.injective

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "Z" => zeroEqualityCycleComponent hπ data D s hs hstart hk hp

/-- None of the actual equality-depth component maps identifies two source points. -/
theorem zeroEqualityCycleComponent_point_injective (i : Fin (2 * s + 2)) :
    Function.Injective (Z i).left := by
  by_cases hi : i.val = 0
  · rw [zeroEqualityCycleComponent, dite_eq_left hi]
    exact finalZeroExteriorComponent_point_injective hπ data D s hs hk hstart
  · by_cases h : i.val ≤ s
    · rw [zeroEqualityCycleComponent, dite_eq_right hi, dite_eq_left h]
      apply equalityComponent_reversal_injective
      exact finalAdjacentComponent_point_injective hπ data D s hs hk _ 0
    · by_cases ht : i.val = s + 1
      · rw [zeroEqualityCycleComponent, dite_eq_right hi, dite_eq_right h, dite_eq_left ht]
        apply equalityComponent_reversal_injective
        exact laurentTerminalProjectiveComponent_injective hπ data D s hs hk hp
      · rw [zeroEqualityCycleComponent, dite_eq_right hi, dite_eq_right h, dite_eq_right ht]
        exact finalAdjacentComponent_point_injective hπ data D s hs hk _ 1

/-- Each component is proper as a morphism into the original finite residue model. -/
theorem zeroEqualityCycleComponent_proper (i : Fin (2 * s + 2)) :
    IsProper (Z i).left := by
  have : IsProper ((Z i).left ≫ p) := by
    have hw : (Z i).left ≫ p = ProjectiveLine.toBase K := (Z i).w
    rw [hw]
    exact PolygonProper.projectiveLine K
  exact IsProper.of_comp _ p

/-- The image of every entire actual component is closed in the original fiber. -/
theorem zeroEqualityCycleComponent_isClosed_range (i : Fin (2 * s + 2)) :
    IsClosed (Set.range (Z i).left) := by
  let _ := zeroEqualityCycleComponent_proper hπ data D s hs hstart hk hp i
  exact (Z i).left.isClosedMap.isClosed_range

/-- Each original projective line is topologically embedded in the finite fiber. -/
theorem zeroEqualityCycleComponent_isClosedEmbedding (i : Fin (2 * s + 2)) :
    IsClosedEmbedding (Z i).left := by
  let _ := zeroEqualityCycleComponent_proper hπ data D s hs hstart hk hp i
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap (Z i).left.continuous
    (zeroEqualityCycleComponent_point_injective hπ data D s hs hstart hk hp i)
    (Z i).left.isClosedMap

/-- Its specified Laurent coordinate is dense in precisely its original full component image. -/
theorem zeroEqualityCycleComponent_closure_torus (i : Fin (2 * s + 2)) :
    closure (Set.range (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫ (Z i).left)) =
      Set.range (Z i).left := by
  let _ := zeroEqualityCycleComponent_proper hπ data D s hs hstart hk hp i
  have he : ((ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫ (Z i).left) :
      _ → finiteGlobalTensorModel hπ data K (s + 1) hs) =
      (Z i).left ∘ (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) := by
    ext x
    rfl
  rw [he, Set.range_comp, ((Z i).left.isClosedMap).closure_image_eq_of_continuous
    (Z i).left.continuous, (ProjectiveLineTopology.torus_dense K).closure_range,
    Set.image_univ]

end FLT.Mazur.WeierstrassDividedDepth

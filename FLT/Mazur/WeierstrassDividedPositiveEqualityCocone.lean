/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedEqualityNodesDistinct
public import FLT.Mazur.WeierstrassDividedPositiveEqualityCycle

/-!
# The actual positive-start equality-depth polygon cocone

The full component and original node coproducts give a commuting cocone over
Spec K. This construction asserts no unproved pushout or fiber comparison.
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
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)

/-- The normalization leg is the coproduct of the complete actual projective components. -/
def positiveEqualityCycleNormalization : PolygonPinching.components K (2 * s + 4) ⟶ Over.mk p :=
  Sigma.desc (positiveEqualityCycleComponent hπ data D s hs hstart hk hp)

/-- Each normalization summand keeps its entire original component parameterization. -/
@[reassoc] theorem positiveEqualityCycleNormalization_ι (i : Fin (2 * s + 4)) :
    PolygonPinching.componentι K (2 * s + 4) i ≫
        positiveEqualityCycleNormalization hπ data D s hs hstart hk hp =
      positiveEqualityCycleComponent hπ data D s hs hstart hk hp i :=
  Sigma.ι_comp_desc _ _

/-- The node leg consists of the original sections in the proved cyclic order. -/
def positiveEqualityCycleNodes : PolygonPinching.nodes K (2 * s + 4) ⟶ Over.mk p :=
  Sigma.desc (fun i => equalityNodeOverSection hπ data D s hs hk
    (positiveEqualityCycleNodeIndex start s hstart i))

/-- Every node summand retains the whole original section over the field. -/
@[reassoc] theorem positiveEqualityCycleNodes_ι (i : Fin (2 * s + 4)) :
    PolygonPinching.nodeι K (2 * s + 4) i ≫
        positiveEqualityCycleNodes hπ data D s hs hstart hk =
      equalityNodeOverSection hπ data D s hs hk (positiveEqualityCycleNodeIndex start s hstart i) :=
  Sigma.ι_comp_desc _ _

/-- The specified polygon pinching diagram commutes for these actual component and node legs. -/
theorem positiveEqualityCycleCocone_condition :
    PolygonPinching.toComponents K (2 * s + 4) (by omega) ≫
        positiveEqualityCycleNormalization hπ data D s hs hstart hk hp =
      PolygonPinching.toNodes K (2 * s + 4) ≫
        positiveEqualityCycleNodes hπ data D s hs hstart hk := by
  apply Sigma.hom_ext
  rintro ⟨i, b⟩
  change PolygonPinching.branchι K (2 * s + 4) i b ≫ _ =
    PolygonPinching.branchι K (2 * s + 4) i b ≫ _
  cases b
  · rw [PolygonPinching.branchι_toComponents_zero_assoc,
      positiveEqualityCycleNormalization_ι, positiveEqualityCycleComponent_zero,
      PolygonPinching.branchι_toNodes_assoc, positiveEqualityCycleNodes_ι]
  · rw [PolygonPinching.branchι_toComponents_infinity_assoc,
      positiveEqualityCycleNormalization_ι, positiveEqualityCycleComponent_next_infinity,
      PolygonPinching.branchι_toNodes_assoc, positiveEqualityCycleNodes_ι]

/-- A constructed pushout cocone, without an assumed universal property. -/
def positiveEqualityCycleCocone :
    PushoutCocone (PolygonPinching.toComponents K (2 * s + 4) (by omega))
      (PolygonPinching.toNodes K (2 * s + 4)) :=
  PushoutCocone.mk (positiveEqualityCycleNormalization hπ data D s hs hstart hk hp)
    (positiveEqualityCycleNodes hπ data D s hs hstart hk)
    (positiveEqualityCycleCocone_condition hπ data D s hs hstart hk hp)

/-- The cyclic list exhausts exactly the complete original node-section family. -/
theorem positiveEqualityCycleNodes_sections_range :
    Set.range (fun i : Fin (2 * s + 4) => equalityNodeOverSection hπ data D s hs hk
        (positiveEqualityCycleNodeIndex start s hstart i)) =
      Set.range (equalityNodeOverSection hπ data D s hs hk) :=
  (positiveEqualityCycleNodeIndex_surjective start s hstart).range_comp
    (equalityNodeOverSection hπ data D s hs hk)

/-- No two cyclic positions give the same actual node section. -/
theorem positiveEqualityCycleNodes_sections_injective :
    Function.Injective (fun i : Fin (2 * s + 4) =>
      equalityNodeOverSection hπ data D s hs hk
        (positiveEqualityCycleNodeIndex start s hstart i)) :=
  (equalityNodeOverSection_injective hπ data D s hs hk).comp
    (positiveEqualityCycleNodeIndex_injective start s hstart)

/-- Distinct cyclic positions give distinct component maps, detected at their zero endpoints. -/
theorem positiveEqualityCycleComponent_index_injective :
    Function.Injective (positiveEqualityCycleComponent hπ data D s hs hstart hk hp) := by
  intro i j he
  have hz := congrArg (fun f => ProjectiveLine.zeroSection K ≫ f) he
  rw [positiveEqualityCycleComponent_zero, positiveEqualityCycleComponent_zero] at hz
  exact positiveEqualityCycleNodes_sections_injective hπ data D s hs hstart hk hz

end FLT.Mazur.WeierstrassDividedDepth

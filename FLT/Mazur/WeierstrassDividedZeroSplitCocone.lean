/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSplitCycle

/-!
# The actual start-zero split-terminal polygon cocone

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
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)

/-- The normalization leg is the coproduct of the complete actual projective components. -/
def zeroSplitCycleNormalization : PolygonPinching.components K (2 * s + 3) ⟶ Over.mk p :=
  Sigma.desc (zeroSplitCycleComponent hπ data D s hs hstart hk hp)

/-- Each normalization summand keeps its entire original component parameterization. -/
@[reassoc] theorem zeroSplitCycleNormalization_ι (i : Fin (2 * s + 3)) :
    PolygonPinching.componentι K (2 * s + 3) i ≫
        zeroSplitCycleNormalization hπ data D s hs hstart hk hp =
      zeroSplitCycleComponent hπ data D s hs hstart hk hp i :=
  Sigma.ι_comp_desc _ _

/-- The node leg consists of the original sections in the proved cyclic order. -/
def zeroSplitCycleNodes : PolygonPinching.nodes K (2 * s + 3) ⟶ Over.mk p :=
  Sigma.desc (fun i => finalNodeOverSection hπ data D s hs hk hp
    (zeroSplitCycleNodeIndex start s i))

/-- Every node summand retains the whole original section over the field. -/
@[reassoc] theorem zeroSplitCycleNodes_ι (i : Fin (2 * s + 3)) :
    PolygonPinching.nodeι K (2 * s + 3) i ≫ zeroSplitCycleNodes hπ data D s hs hk hp =
      finalNodeOverSection hπ data D s hs hk hp (zeroSplitCycleNodeIndex start s i) :=
  Sigma.ι_comp_desc _ _

/-- The specified polygon pinching diagram commutes for these actual component and node legs. -/
theorem zeroSplitCycleCocone_condition :
    PolygonPinching.toComponents K (2 * s + 3) (by omega) ≫
        zeroSplitCycleNormalization hπ data D s hs hstart hk hp =
      PolygonPinching.toNodes K (2 * s + 3) ≫ zeroSplitCycleNodes hπ data D s hs hk hp := by
  apply Sigma.hom_ext
  rintro ⟨i, b⟩
  change PolygonPinching.branchι K (2 * s + 3) i b ≫ _ =
    PolygonPinching.branchι K (2 * s + 3) i b ≫ _
  cases b
  · rw [PolygonPinching.branchι_toComponents_zero_assoc,
      zeroSplitCycleNormalization_ι, zeroSplitCycleComponent_zero,
      PolygonPinching.branchι_toNodes_assoc, zeroSplitCycleNodes_ι]
  · rw [PolygonPinching.branchι_toComponents_infinity_assoc,
      zeroSplitCycleNormalization_ι, zeroSplitCycleComponent_next_infinity,
      PolygonPinching.branchι_toNodes_assoc, zeroSplitCycleNodes_ι]

/-- A constructed pushout cocone, without an assumed universal property. -/
def zeroSplitCycleCocone :
    PushoutCocone (PolygonPinching.toComponents K (2 * s + 3) (by omega))
      (PolygonPinching.toNodes K (2 * s + 3)) :=
  PushoutCocone.mk (zeroSplitCycleNormalization hπ data D s hs hstart hk hp)
    (zeroSplitCycleNodes hπ data D s hs hk hp)
    (zeroSplitCycleCocone_condition hπ data D s hs hstart hk hp)

include hstart in
/-- The cyclic list exhausts exactly the complete original node-section family. -/
theorem zeroSplitCycleNodes_sections_range :
    Set.range (fun i : Fin (2 * s + 3) => finalNodeOverSection hπ data D s hs hk hp
        (zeroSplitCycleNodeIndex start s i)) =
      Set.range (finalNodeOverSection hπ data D s hs hk hp) :=
  (zeroSplitCycleNodeIndex_surjective start s hstart).range_comp
    (finalNodeOverSection hπ data D s hs hk hp)

/-- No two cyclic positions give the same actual node section. -/
theorem zeroSplitCycleNodes_sections_injective :
    Function.Injective (fun i : Fin (2 * s + 3) =>
      finalNodeOverSection hπ data D s hs hk hp (zeroSplitCycleNodeIndex start s i)) :=
  (finalNodeOverSection_injective hπ data D s hs hk hp).comp
    (zeroSplitCycleNodeIndex_injective start s)

/-- Distinct cyclic positions give distinct component maps, detected at their zero endpoints. -/
theorem zeroSplitCycleComponent_index_injective :
    Function.Injective (zeroSplitCycleComponent hπ data D s hs hstart hk hp) := by
  intro i j he
  have hz := congrArg (fun f => ProjectiveLine.zeroSection K ≫ f) he
  rw [zeroSplitCycleComponent_zero, zeroSplitCycleComponent_zero] at hz
  exact zeroSplitCycleNodes_sections_injective hπ data D s hs hk hp hz

end FLT.Mazur.WeierstrassDividedDepth

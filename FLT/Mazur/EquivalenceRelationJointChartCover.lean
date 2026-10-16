/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationJointChartDomains
public import FLT.Mazur.EquivalenceRelationJointFrameCover

/-!
# Exhaustive comparisons for independent source chart refinements

Restrict the common-frame family to the full inverse image of both charts.
These actual etale maps still cover the entire original mixed chart relation.
No pointwise selection replaces either chart or its pulled-back boundary.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (U : (source p q I o).Opens) (V : (source p q J o').Opens)

/-- The entire original mixed relation between the two independently chosen charts. -/
def mixedChartOpen : (relation p q I J o o').Opens :=
  fst p q I J o o' ⁻¹ᵁ U ⊓ snd p q I J o o' ⁻¹ᵁ V

/-- The constructed common-chart domain is exactly the full inverse image. -/
theorem jointChartOpen_eq_preimage (c : JointIndex I J) :
    jointChartOpen e o o' c.2.val.1 c.2.val.2 U V =
      jointMap e o o' c ⁻¹ᵁ mixedChartOpen o o' U V := by
  change _ = (jointMap e o o' c ⁻¹ᵁ (fst p q I J o o' ⁻¹ᵁ U)) ⊓
    (jointMap e o o' c ⁻¹ᵁ (snd p q I J o o' ⁻¹ᵁ V))
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
  simp only [jointMap, jointGraph_fst, jointGraph_snd, jointChartOpen]

/-- The full common-frame overlap maps to the original mixed chart relation. -/
def jointChartMap (c : JointIndex I J) :
    (jointChartOpen e o o' c.2.val.1 c.2.val.2 U V).toScheme ⟶
      (mixedChartOpen o o' U V).toScheme :=
  (jointMap e o o' c).resLE _ _ (jointChartOpen_eq_preimage e o o' U V c).le

/-- The chart comparison still has precisely its original common-frame graph. -/
@[reassoc] theorem jointChartMap_inclusion (c : JointIndex I J) :
    jointChartMap e o o' U V c ≫ (mixedChartOpen o o' U V).ι =
      (jointChartOpen e o o' c.2.val.1 c.2.val.2 U V).ι ≫ jointMap e o o' c :=
  Scheme.Hom.resLE_comp_ι _ _

variable [Etale p]

instance jointChartMap_etale (c : JointIndex I J) : Etale (jointChartMap e o o' U V c) := by
  unfold jointChartMap
  infer_instance

/-- Every point in the entire original mixed chart relation has a common-chart preimage. -/
theorem jointChartMap_covers (x : (mixedChartOpen o o' U V).toScheme) :
    ∃ (c : JointIndex I J)
      (y : (jointChartOpen e o o' c.2.val.1 c.2.val.2 U V).toScheme),
      jointChartMap e o o' U V c y = x := by
  obtain ⟨c, y, hy⟩ := jointMap_covers e o o' x.val
  have hmem : y ∈ jointChartOpen e o o' c.2.val.1 c.2.val.2 U V := by
    rw [jointChartOpen_eq_preimage]
    change jointMap e o o' c y ∈ mixedChartOpen o o' U V
    rw [hy]
    exact x.property
  refine ⟨c, ⟨y, hmem⟩, ?_⟩
  apply Subtype.ext
  exact (congrArg (fun f ↦ f ⟨y, hmem⟩)
    (jointChartMap_inclusion e o o' U V c)).trans hy

/-- Independent chart refinements inherit an exhaustive finite common-frame etale family. -/
def jointChartCover :
    (mixedChartOpen o o' U V).toScheme.Cover (Scheme.precoverage @Etale) :=
  Scheme.Cover.mkOfCovers _
    (fun c : JointIndex I J ↦ (jointChartOpen e o o' c.2.val.1 c.2.val.2 U V).toScheme)
    (jointChartMap e o o' U V) (jointChartMap_covers e o o' U V) (fun _ ↦ inferInstance)

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames

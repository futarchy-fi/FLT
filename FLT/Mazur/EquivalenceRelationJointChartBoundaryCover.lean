/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationJointChartCover
public import FLT.Mazur.EquivalenceRelationJointBoundaryCover

/-!
# Exhaustive exact boundary comparisons after independent chart refinement

The full common-chart boundaries cover the entire original mixed boundary
between the two charts. The morphisms are restrictions of the actual Cartesian
boundary comparison, preserving the entire original section domain.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (U : (source p q I o).Opens) (V : (source p q J o').Opens) (i : B ⟶ A)

/-- The full original mixed boundary between the independent source charts. -/
def mixedChartBoundaryOpen : (jointBoundaryTarget (p := p) (q := q) o o' i).Opens :=
  jointBoundaryTargetInclusion (p := p) (q := q) o o' i ⁻¹ᵁ mixedChartOpen o o' U V

/-- Each common-chart boundary is the entire inverse image of the original chart boundary. -/
theorem jointChartBoundaryOpen_eq_preimage (c : JointIndex I J) :
    InvariantBoundary.inclusion (Fin c.1.val) (c.2.val.1 o) i ⁻¹ᵁ
      jointChartOpen e o o' c.2.val.1 c.2.val.2 U V =
        jointBoundaryMap e o o' i c ⁻¹ᵁ mixedChartBoundaryOpen o o' U V i := by
  rw [mixedChartBoundaryOpen, ← Scheme.Hom.comp_preimage,
    jointBoundaryMap_inclusion, Scheme.Hom.comp_preimage, ← jointChartOpen_eq_preimage]

/-- The actual restricted boundary comparison, retaining all nilpotents. -/
def jointChartBoundaryMap (c : JointIndex I J) :
    (InvariantBoundary.inclusion (Fin c.1.val) (c.2.val.1 o) i ⁻¹ᵁ
      jointChartOpen e o o' c.2.val.1 c.2.val.2 U V).toScheme ⟶
        (mixedChartBoundaryOpen o o' U V i).toScheme :=
  (jointBoundaryMap e o o' i c).resLE _ _
    (jointChartBoundaryOpen_eq_preimage e o o' U V i c).le

/-- Its original closed comparison is unchanged on the full open domain. -/
@[reassoc] theorem jointChartBoundaryMap_inclusion (c : JointIndex I J) :
    jointChartBoundaryMap e o o' U V i c ≫ (mixedChartBoundaryOpen o o' U V i).ι =
      (InvariantBoundary.inclusion (Fin c.1.val) (c.2.val.1 o) i ⁻¹ᵁ
        jointChartOpen e o o' c.2.val.1 c.2.val.2 U V).ι ≫ jointBoundaryMap e o o' i c :=
  Scheme.Hom.resLE_comp_ι _ _

variable [Etale p]

instance jointChartBoundaryMap_etale (c : JointIndex I J) :
    Etale (jointChartBoundaryMap e o o' U V i c) := by
  unfold jointChartBoundaryMap
  infer_instance

/-- Every original boundary point between the two charts has an exact common-chart preimage. -/
theorem jointChartBoundaryMap_covers (x : (mixedChartBoundaryOpen o o' U V i).toScheme) :
    ∃ (c : JointIndex I J)
      (y : (InvariantBoundary.inclusion (Fin c.1.val) (c.2.val.1 o) i ⁻¹ᵁ
        jointChartOpen e o o' c.2.val.1 c.2.val.2 U V).toScheme),
      jointChartBoundaryMap e o o' U V i c y = x := by
  obtain ⟨c, y, hy⟩ := jointBoundaryMap_covers e o o' i x.val
  have hmem : y ∈ InvariantBoundary.inclusion (Fin c.1.val) (c.2.val.1 o) i ⁻¹ᵁ
      jointChartOpen e o o' c.2.val.1 c.2.val.2 U V := by
    rw [jointChartBoundaryOpen_eq_preimage]
    change jointBoundaryMap e o o' i c y ∈ mixedChartBoundaryOpen o o' U V i
    rw [hy]
    exact x.property
  refine ⟨c, ⟨y, hmem⟩, ?_⟩
  apply Subtype.ext
  exact (congrArg (fun f ↦ f ⟨y, hmem⟩)
    (jointChartBoundaryMap_inclusion e o o' U V i c)).trans hy

/-- An exhaustive finite etale family for the entire original mixed chart boundary. -/
def jointChartBoundaryCover :
    (mixedChartBoundaryOpen o o' U V i).toScheme.Cover (Scheme.precoverage @Etale) :=
  Scheme.Cover.mkOfCovers _ (fun c : JointIndex I J ↦
    (InvariantBoundary.inclusion (Fin c.1.val) (c.2.val.1 o) i ⁻¹ᵁ
      jointChartOpen e o o' c.2.val.1 c.2.val.2 U V).toScheme)
    (jointChartBoundaryMap e o o' U V i) (jointChartBoundaryMap_covers e o o' U V i)
    (fun _ ↦ inferInstance)

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames

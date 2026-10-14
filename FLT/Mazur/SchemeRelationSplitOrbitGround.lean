/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationSplitOrbitAffineSeed
public import FLT.Mazur.SchemeSplitSeedGroundChart

/-!
# Split orbits inside genuine ground changes

The constructed orbit immerses into the actual ground source. Restricting
the full ground relation to this orbit gives the same scheme relation as
restricting by coefficient equality. The isomorphism keeps both independent
endpoints and the original arrow; it does not discard nilpotent tests.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationSplitOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T G Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A.left ⟶ T)
  (h : p.left ≫ w = q.left ≫ w) (i : T ⟶ G) (a : Z ⟶ A.left)

include h in
/-- The old relation coequalizes the actual ground map as a scheme morphism. -/
theorem ground_condition : p.left ≫ (w ≫ i) = q.left ≫ (w ≫ i) := by
  simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ i) h

/-- The orbit keeps its source and new ground coordinates in the genuine ground change. -/
def groundInclusion : pullback q.left a ⟶
    SchemeSplitSeedGroundComparison.groundSource w i a :=
  inclusion w h a ≫ SchemeSplitSeedGroundComparison.comparison w i a

@[reassoc]
theorem groundInclusion_source : groundInclusion w h i a ≫
    SchemeSplitSeedGroundComparison.groundToSource w i a =
      SchemeRelationEtaleBranchPropagation.branch p.left q.left a := by
  rw [groundInclusion, Category.assoc,
    SchemeSplitSeedGroundComparison.comparison_source, inclusion_source]

@[reassoc]
theorem groundInclusion_projection : groundInclusion w h i a ≫
    SchemeSplitSeedGroundComparison.groundProjection w i a = pullback.snd q.left a := by
  rw [groundInclusion, Category.assoc,
    SchemeSplitSeedGroundComparison.comparison_projection, inclusion_projection]

@[reassoc]
theorem sectionMap_groundInclusion : sectionMap e a ≫ groundInclusion w h i a =
    SchemeSplitSeedGroundComparison.groundSeed w i a := by
  rw [groundInclusion, sectionMap_inclusion_assoc,
    SchemeSplitSeedGroundComparison.seed_comparison]

variable [Mono (pullback.lift p.left q.left h)]

/-- Original kernel monicity is preserved when passing to the larger ground kernel. -/
theorem groundKernel_mono :
    Mono (pullback.lift p.left q.left (ground_condition w h i)) := by
  have hm : pullback.lift p.left q.left (ground_condition w h i) =
      pullback.lift p.left q.left h ≫ pullback.mapDesc w w i := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id]
  rw [hm]
  infer_instance

/-- The two full relation restrictions are isomorphic, not merely equal on field-valued points. -/
def fullGroundRelationIso : fullRelation w h a ≅
    fullRelation (w ≫ i) (ground_condition w h i) a := by
  let _ := groundKernel_mono w h i
  exact fullKernelIso e w h a ≪≫ (fullKernelIso e (w ≫ i) (ground_condition w h i) a).symm

@[reassoc]
theorem fullGroundRelationIso_comparison : (fullGroundRelationIso e w h i a).hom ≫
    fullComparison (w ≫ i) (ground_condition w h i) a = fullComparison w h a := by
  change (fullComparison w h a ≫ kernelLift e (w ≫ i) (ground_condition w h i) a) ≫
    fullComparison (w ≫ i) (ground_condition w h i) a = _
  rw [Category.assoc, kernelLift_comparison, Category.comp_id]

@[reassoc]
theorem fullComparison_kernelArrow : fullComparison w h a ≫ kernelArrow e a =
    fullArrow w h a := by
  rw [← kernelLift_arrow e w h a, ← Category.assoc]
  change (fullKernelIso e w h a).hom ≫ (fullKernelIso e w h a).inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]

@[reassoc]
theorem fullGroundRelationIso_arrow : (fullGroundRelationIso e w h i a).hom ≫
    fullArrow (w ≫ i) (ground_condition w h i) a = fullArrow w h a := by
  change (fullComparison w h a ≫ kernelLift e (w ≫ i) (ground_condition w h i) a) ≫
    fullArrow (w ≫ i) (ground_condition w h i) a = _
  rw [Category.assoc, kernelLift_arrow, fullComparison_kernelArrow]

variable [IsSeparated i]

/-- Unramified old coefficients give an immersion of the entire orbit into the ground source. -/
theorem groundInclusion_isImmersion [Etale p.left] [Etale a]
    [FormallyUnramified w] [LocallyOfFiniteType w] :
    IsImmersion (groundInclusion w h i a) := by
  let _ := inclusion_isOpenImmersion w h a
  exact inferInstanceAs (IsImmersion
    (inclusion w h a ≫ SchemeSplitSeedGroundComparison.comparison w i a))

/-- Every constructed affine split selection immerses into the actual ground change. -/
theorem affineGround_isImmersion [Etale p.left] [Etale a]
    [FormallyUnramified w] [LocallyOfFiniteType w] (z : Z) :
    IsImmersion (affineToOrbit e a z ≫ groundInclusion w h i a) := by
  let _ := groundInclusion_isImmersion w h i a
  infer_instance

end FLT.Mazur.SchemeRelationSplitOrbit

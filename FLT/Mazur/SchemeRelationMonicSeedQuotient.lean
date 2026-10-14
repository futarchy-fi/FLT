/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationMonicSeedEffective
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# An actual etale quotient of the propagated monic seed source

The full restricted original relation has an effective quotient over the
open image of the seed orbit source. The quotient and its surjective etale
projection are constructed, with no generic coverage assumption. The new
source maps to the unrestricted original source by the original branch.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationMonicSeedKernel
set_option backward.isDefEq.respectTransparency false
variable {S T Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A.left ⟶ T)
  (h : p.left ≫ w = q.left ≫ w) (a : Z ⟶ A.left)
  [Etale q.left] [Etale (a ≫ w)]
local notation "b" => SchemeRelationEtaleBranchPropagation.branch p.left q.left a
local notation "p'" => SchemeRelationRestriction.fst p.left q.left b
local notation "q'" => SchemeRelationRestriction.snd p.left q.left b

/-- The actual coefficient image of the propagated original source. -/
def quotientOpen : T.Opens := by
  let _ := SchemeRelationEtaleBranchPropagation.branch_target_etale p.left q.left w h a
  exact ⟨Set.range (b ≫ w), (b ≫ w).isOpenMap.isOpen_range⟩

/-- The constructed quotient projection keeps the original coefficient morphism. -/
def quotientProjection : pullback q.left a ⟶ (quotientOpen w h a).toScheme :=
  IsOpenImmersion.lift (quotientOpen w h a).ι (b ≫ w) (by simp [quotientOpen])

@[reassoc]
theorem quotientProjection_ι : quotientProjection w h a ≫ (quotientOpen w h a).ι =
    b ≫ w := IsOpenImmersion.lift_fac _ _ _

instance quotientProjection_etale : Etale (quotientProjection w h a) := by
  let _ : Etale (quotientProjection w h a ≫ (quotientOpen w h a).ι) := by
    rw [quotientProjection_ι]
    exact SchemeRelationEtaleBranchPropagation.branch_target_etale p.left q.left w h a
  exact Etale.of_comp (quotientProjection w h a) (quotientOpen w h a).ι

instance quotientProjection_surjective : Surjective (quotientProjection w h a) := ⟨by
  rintro ⟨y, z, hz⟩
  refine ⟨z, ?_⟩
  apply (quotientOpen w h a).ι.injective
  exact (congrArg (fun t ↦ t z) (quotientProjection_ι w h a)).trans hz⟩

variable [Mono (a ≫ w)] [Mono (pullback.lift p.left q.left h)]
local notation "π" => quotientProjection w h a

omit [Mono (a ≫ w)] [Mono (pullback.lift p.left q.left h)] in
/-- The quotient coequalizes every original restricted relation arrow. -/
theorem quotient_condition : p' ≫ π = q' ≫ π := by
  apply (cancel_mono (quotientOpen w h a).ι).mp
  simp only [Category.assoc, quotientProjection_ι]
  exact branch_condition w h a

include e in
/-- The complete original relation on the propagated source is its actual quotient kernel. -/
theorem quotient_isPullback : IsPullback p' q' π π := by
  have H (c : PullbackCone π π) : c.fst ≫ (b ≫ w) = c.snd ≫ (b ≫ w) := by
    simpa only [Category.assoc, quotientProjection_ι] using
      congrArg (fun t ↦ t ≫ (quotientOpen w h a).ι) c.condition
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (quotient_condition w h a)
    (fun c ↦ branchLift e w h a c.fst c.snd (H c))
    (fun c ↦ branchLift_fst e w h a c.fst c.snd (H c))
    (fun c ↦ branchLift_snd e w h a c.fst c.snd (H c)) ?_)
  intro c z hz₁ hz₂
  apply branch_hom_ext w h a
  · exact hz₁.trans (branchLift_fst e w h a c.fst c.snd (H c)).symm
  · exact hz₂.trans (branchLift_snd e w h a c.fst c.snd (H c)).symm

end FLT.Mazur.SchemeRelationMonicSeedKernel

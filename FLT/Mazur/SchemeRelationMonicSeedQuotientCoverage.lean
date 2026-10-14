/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationMonicSeedQuotient

/-!
# Seed points and coefficient coverage of the constructed quotient

Original identity arrows put every seed point in the propagated source.
Consequently the constructed quotient is precisely the seed coefficient
image, and is nonempty for a nonempty seed. No generic kernel coverage or
integral source premise is needed for this reselected quotient.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationMonicSeedKernel
set_option backward.isDefEq.respectTransparency false
variable {S T Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A.left ⟶ T)
  (h : p.left ≫ w = q.left ≫ w) (a : Z ⟶ A.left)
local notation "b" => SchemeRelationEtaleBranchPropagation.branch p.left q.left a

/-- Identity arrows insert the original seed into its propagated source. -/
def seedToBranch : Z ⟶ pullback q.left a :=
  pullback.lift (a ≫ e.r.left) (𝟙 Z) (by
    rw [Category.assoc, ← Over.comp_left, e.reflexivity₂, Over.id_left,
      Category.comp_id, Category.id_comp])

@[reassoc]
theorem seedToBranch_source : seedToBranch e a ≫ b = a := by
  rw [SchemeRelationEtaleBranchPropagation.branch, ← Category.assoc,
    seedToBranch, pullback.lift_fst, Category.assoc, ← Over.comp_left,
    e.reflexivity₁, Over.id_left, Category.comp_id]

include e h

/-- Propagation changes source coverage but retains precisely the seed coefficient image. -/
theorem branch_target_range : Set.range (b ≫ w) = Set.range (a ≫ w) := by
  apply Set.Subset.antisymm
  · rw [SchemeRelationEtaleBranchPropagation.branch_comp p.left q.left w h a]
    rintro _ ⟨z, rfl⟩
    exact ⟨pullback.snd q.left a z, rfl⟩
  · rintro _ ⟨z, rfl⟩
    refine ⟨seedToBranch e a z, ?_⟩
    exact congrArg (fun t ↦ t z)
      (by rw [← Category.assoc, seedToBranch_source] :
        seedToBranch e a ≫ (b ≫ w) = a ≫ w)

variable [Etale q.left] [Etale (a ≫ w)]

/-- The actual quotient target is the open image of the original seed coefficients. -/
theorem quotientOpen_range : (quotientOpen w h a : Set T) = Set.range (a ≫ w) :=
  branch_target_range e w h a

/-- Every actual seed produces a nonempty quotient of its full propagated relation. -/
theorem quotientOpen_nonempty [Nonempty Z] :
    (quotientOpen w h a : Set T).Nonempty := by
  rw [quotientOpen_range e w h a]
  exact Set.range_nonempty _

/-- The quotient retains the original coefficient of each seed point literally. -/
theorem quotient_seed_point (z : Z) :
    (quotientOpen w h a).ι (quotientProjection w h a (seedToBranch e a z)) = (a ≫ w) z := by
  change (seedToBranch e a ≫ (quotientProjection w h a ≫ (quotientOpen w h a).ι)) z = _
  rw [quotientProjection_ι, ← Category.assoc, seedToBranch_source]

end FLT.Mazur.SchemeRelationMonicSeedKernel

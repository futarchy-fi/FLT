/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductSchemeLaws
public import FLT.Mazur.CyclicCharacteristicDisjointAction

/-!
# Assembling all ordered-pair comparison arrows

The arrow scheme is the disjoint union of the four actual comparison schemes.
Source, target, identity, and inversion assemble over normalizedDisjointSource.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The arrow scheme retains all specified compatible comparisons in every ordered pair. -/
def disjointComparisonArrows : Scheme := ∐ (fun p : Bool × Bool ↦ productSubgroupScheme n p.1 p.2)

/-- Inclusion of a particular ordered-pair comparison scheme. -/
def disjointComparisonInclusion (b c : Bool) :
    productSubgroupScheme n b c ⟶ disjointComparisonArrows n :=
  Sigma.ι (fun p : Bool × Bool ↦ productSubgroupScheme n p.1 p.2) (b, c)

/-- Source map to the assembled normalized atlas. -/
def disjointComparisonSource : disjointComparisonArrows n ⟶ normalizedDisjointSource n :=
  Sigma.desc (fun p ↦ productArrowSource n p.1 p.2 ≫ normalizedDisjointInclusion n p.1)

/-- Target map to the assembled normalized atlas. -/
def disjointComparisonTarget : disjointComparisonArrows n ⟶ normalizedDisjointSource n :=
  Sigma.desc (fun p ↦ productArrowTarget n p.1 p.2 ≫ normalizedDisjointInclusion n p.2)

/-- The identity section assembled from the two normalized bases. -/
def disjointComparisonIdentity : normalizedDisjointSource n ⟶ disjointComparisonArrows n :=
  Sigma.desc (fun b ↦ productIdentityMap n b ≫ disjointComparisonInclusion n b b)

/-- Inversion assembled from the actual ordered-pair inversion morphisms. -/
def disjointComparisonInverse : disjointComparisonArrows n ⟶ disjointComparisonArrows n :=
  Sigma.desc (fun p ↦ productInverseMap n p.1 p.2 ≫ disjointComparisonInclusion n p.2 p.1)

/-- Source on each component is the original source map. -/
@[reassoc] theorem disjointComparisonInclusion_source (b c : Bool) :
    disjointComparisonInclusion n b c ≫ disjointComparisonSource n =
      productArrowSource n b c ≫ normalizedDisjointInclusion n b := Sigma.ι_comp_desc _ _

/-- Target on each component is the original target map. -/
@[reassoc] theorem disjointComparisonInclusion_target (b c : Bool) :
    disjointComparisonInclusion n b c ≫ disjointComparisonTarget n =
      productArrowTarget n b c ≫ normalizedDisjointInclusion n c := Sigma.ι_comp_desc _ _

/-- Identity on each base component is the constructed identity section. -/
@[reassoc] theorem normalizedDisjointInclusion_identity (b : Bool) :
    normalizedDisjointInclusion n b ≫ disjointComparisonIdentity n =
      productIdentityMap n b ≫ disjointComparisonInclusion n b b := Sigma.ι_comp_desc _ _

/-- Inversion on each arrow component is the constructed inversion morphism. -/
@[reassoc] theorem disjointComparisonInclusion_inverse (b c : Bool) :
    disjointComparisonInclusion n b c ≫ disjointComparisonInverse n =
      productInverseMap n b c ≫ disjointComparisonInclusion n c b := Sigma.ι_comp_desc _ _

/-- The assembled identity section has identity source. -/
@[reassoc] theorem disjointComparisonIdentity_source :
    disjointComparisonIdentity n ≫ disjointComparisonSource n = 𝟙 _ := by
  apply Sigma.hom_ext
  intro b
  change normalizedDisjointInclusion n b ≫ _ = normalizedDisjointInclusion n b ≫ 𝟙 _
  simp only [normalizedDisjointInclusion_identity_assoc, disjointComparisonInclusion_source,
    productIdentityMap_source_assoc,
    Category.comp_id]

/-- The assembled identity section has identity target. -/
@[reassoc] theorem disjointComparisonIdentity_target :
    disjointComparisonIdentity n ≫ disjointComparisonTarget n = 𝟙 _ := by
  apply Sigma.hom_ext
  intro b
  change normalizedDisjointInclusion n b ≫ _ = normalizedDisjointInclusion n b ≫ 𝟙 _
  simp only [normalizedDisjointInclusion_identity_assoc, disjointComparisonInclusion_target,
    productIdentityMap_target_assoc,
    Category.comp_id]

/-- Assembled inversion exchanges source and target. -/
@[reassoc] theorem disjointComparisonInverse_source :
    disjointComparisonInverse n ≫ disjointComparisonSource n = disjointComparisonTarget n := by
  apply Sigma.hom_ext
  intro p
  change disjointComparisonInclusion n p.1 p.2 ≫ _ =
    disjointComparisonInclusion n p.1 p.2 ≫ disjointComparisonTarget n
  simp only [disjointComparisonInclusion_inverse_assoc,
    disjointComparisonInclusion_source, productInverseMap_source_assoc,
    disjointComparisonInclusion_target]

/-- Assembled inversion exchanges target and source. -/
@[reassoc] theorem disjointComparisonInverse_target :
    disjointComparisonInverse n ≫ disjointComparisonTarget n = disjointComparisonSource n := by
  apply Sigma.hom_ext
  intro p
  change disjointComparisonInclusion n p.1 p.2 ≫ _ =
    disjointComparisonInclusion n p.1 p.2 ≫ disjointComparisonSource n
  simp only [disjointComparisonInclusion_inverse_assoc,
    disjointComparisonInclusion_target, productInverseMap_target_assoc,
    disjointComparisonInclusion_source]

/-- Assembled inversion is involutive. -/
@[reassoc] theorem disjointComparisonInverse_involutive :
    disjointComparisonInverse n ≫ disjointComparisonInverse n = 𝟙 _ := by
  apply Sigma.hom_ext
  intro p
  change disjointComparisonInclusion n p.1 p.2 ≫ _ =
    disjointComparisonInclusion n p.1 p.2 ≫ 𝟙 _
  simp only [disjointComparisonInclusion_inverse_assoc,
    disjointComparisonInclusion_inverse, productInverseMap_involutive_assoc, Category.comp_id]

end FLT.Mazur.CyclicCharacteristicAtlas

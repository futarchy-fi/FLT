/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointCompositionTests

/-!
# Global unit diagrams for the normalized comparison atlas

The two unit insertions are actual morphisms into the global composable scheme.
Their composites with composition are identities on the entire arrow scheme.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n
local notation "unit" => disjointComparisonIdentity n

/-- Insert the identity at the source before the given global arrow. -/
def disjointLeftUnitInsertion : disjointComparisonArrows n ⟶ disjointComposableScheme n :=
  disjointComposableLift n (src ≫ unit) (𝟙 _) (by
    rw [Category.assoc, disjointComparisonIdentity_target, Category.comp_id, Category.id_comp])

/-- Insert the identity at the target after the given global arrow. -/
def disjointRightUnitInsertion : disjointComparisonArrows n ⟶ disjointComposableScheme n :=
  disjointComposableLift n (𝟙 _) (tgt ≫ unit) (by
    rw [Category.assoc, disjointComparisonIdentity_source, Category.comp_id, Category.id_comp])

/-- Left unit insertion restricts to the original component insertion. -/
theorem disjointComparisonInclusion_leftUnit (b c : Bool) :
    disjointComparisonInclusion n b c ≫ disjointLeftUnitInsertion n =
      productComposableLift n b b c (productArrowId n (productArrowSource n b c))
        (productUniversalArrow n b c) ≫ disjointComposableInclusion n b b c := by
  apply pullback.hom_ext
  · simp only [disjointLeftUnitInsertion, Category.assoc, disjointComposableLift_first,
      disjointComparisonInclusion_source_assoc, normalizedDisjointInclusion_identity,
      disjointComposableInclusion_first, productComposableLift_first_assoc,
      ← productIdentityMap_apply, Category.assoc]
  · simp only [disjointLeftUnitInsertion, Category.assoc, disjointComposableLift_second,
      Category.comp_id, disjointComposableInclusion_second, productComposableLift_second_assoc]
    exact (Category.id_comp _).symm

/-- Right unit insertion restricts to the original component insertion. -/
theorem disjointComparisonInclusion_rightUnit (b c : Bool) :
    disjointComparisonInclusion n b c ≫ disjointRightUnitInsertion n =
      productComposableLift n b c c (productUniversalArrow n b c)
        (productArrowId n (productArrowTarget n b c)) ≫ disjointComposableInclusion n b c c := by
  apply pullback.hom_ext
  · simp only [disjointRightUnitInsertion, Category.assoc, disjointComposableLift_first,
      Category.comp_id, disjointComposableInclusion_first, productComposableLift_first_assoc]
    exact (Category.id_comp _).symm
  · simp only [disjointRightUnitInsertion, Category.assoc, disjointComposableLift_second,
      disjointComparisonInclusion_target_assoc, normalizedDisjointInclusion_identity,
      disjointComposableInclusion_second, productComposableLift_second_assoc,
      ← productIdentityMap_apply, Category.assoc]

/-- The global left unit diagram commutes on the actual arrow scheme. -/
@[reassoc] theorem disjointCompositionMap_left_unit :
    disjointLeftUnitInsertion n ≫ disjointCompositionMap n = 𝟙 _ := by
  apply Sigma.hom_ext
  intro p
  change disjointComparisonInclusion n p.1 p.2 ≫ _ =
    disjointComparisonInclusion n p.1 p.2 ≫ 𝟙 _
  rw [← Category.assoc, disjointComparisonInclusion_leftUnit, Category.assoc,
    disjointComposableInclusion_composition, ← Category.assoc,
    productCompositionMap_universal_left_unit, Category.id_comp, Category.comp_id]

/-- The global right unit diagram commutes on the actual arrow scheme. -/
@[reassoc] theorem disjointCompositionMap_right_unit :
    disjointRightUnitInsertion n ≫ disjointCompositionMap n = 𝟙 _ := by
  apply Sigma.hom_ext
  intro p
  change disjointComparisonInclusion n p.1 p.2 ≫ _ =
    disjointComparisonInclusion n p.1 p.2 ≫ 𝟙 _
  rw [← Category.assoc, disjointComparisonInclusion_rightUnit, Category.assoc,
    disjointComposableInclusion_composition, ← Category.assoc,
    productCompositionMap_universal_right_unit, Category.id_comp, Category.comp_id]

end FLT.Mazur.CyclicCharacteristicAtlas

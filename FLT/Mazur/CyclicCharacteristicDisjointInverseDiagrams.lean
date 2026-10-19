/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicDisjointUnitDiagrams

/-!
# Global inverse diagrams for the normalized comparison atlas

Composing either an arrow with its inverse or its inverse with that arrow gives
the corresponding identity section, as equations of actual scheme morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n
local notation "inv" => disjointComparisonInverse n

/-- Pair an arrow with its inverse, in that order. -/
def disjointRightInverseInsertion : disjointComparisonArrows n ⟶ disjointComposableScheme n :=
  disjointComposableLift n (𝟙 _) inv (by
    rw [Category.id_comp, disjointComparisonInverse_source])

/-- Pair an inverse with the original arrow, in that order. -/
def disjointLeftInverseInsertion : disjointComparisonArrows n ⟶ disjointComposableScheme n :=
  disjointComposableLift n inv (𝟙 _) (by
    rw [Category.id_comp, disjointComparisonInverse_target])

/-- Right inverse insertion retains the original component and its actual inverse. -/
theorem disjointComparisonInclusion_rightInverse (b c : Bool) :
    disjointComparisonInclusion n b c ≫ disjointRightInverseInsertion n =
      productComposableLift n b c b (productUniversalArrow n b c)
        (productArrowInv n (productUniversalArrow n b c)) ≫
          disjointComposableInclusion n b c b := by
  apply pullback.hom_ext
  · simp only [disjointRightInverseInsertion, Category.assoc, disjointComposableLift_first,
      Category.comp_id, disjointComposableInclusion_first, productComposableLift_first_assoc]
    exact (Category.id_comp _).symm
  · simp only [disjointRightInverseInsertion, Category.assoc, disjointComposableLift_second,
      disjointComparisonInclusion_inverse, disjointComposableInclusion_second,
      productComposableLift_second_assoc]
    rfl

/-- Left inverse insertion retains the actual inverse and original component. -/
theorem disjointComparisonInclusion_leftInverse (b c : Bool) :
    disjointComparisonInclusion n b c ≫ disjointLeftInverseInsertion n =
      productComposableLift n c b c (productArrowInv n (productUniversalArrow n b c))
        (productUniversalArrow n b c) ≫ disjointComposableInclusion n c b c := by
  apply pullback.hom_ext
  · simp only [disjointLeftInverseInsertion, Category.assoc, disjointComposableLift_first,
      disjointComparisonInclusion_inverse, disjointComposableInclusion_first,
      productComposableLift_first_assoc]
    rfl
  · simp only [disjointLeftInverseInsertion, Category.assoc, disjointComposableLift_second,
      Category.comp_id, disjointComposableInclusion_second, productComposableLift_second_assoc]
    exact (Category.id_comp _).symm

/-- The global right inverse diagram gives the identity at the source. -/
@[reassoc] theorem disjointCompositionMap_right_inverse :
    disjointRightInverseInsertion n ≫ disjointCompositionMap n =
      src ≫ disjointComparisonIdentity n := by
  apply Sigma.hom_ext
  intro p
  change disjointComparisonInclusion n p.1 p.2 ≫ _ =
    disjointComparisonInclusion n p.1 p.2 ≫ (src ≫ disjointComparisonIdentity n)
  rw [← Category.assoc, disjointComparisonInclusion_rightInverse, Category.assoc,
    disjointComposableInclusion_composition, ← Category.assoc,
    productCompositionMap_right_inverse, Category.assoc,
    disjointComparisonInclusion_source_assoc, normalizedDisjointInclusion_identity]

/-- The global left inverse diagram gives the identity at the target. -/
@[reassoc] theorem disjointCompositionMap_left_inverse :
    disjointLeftInverseInsertion n ≫ disjointCompositionMap n =
      tgt ≫ disjointComparisonIdentity n := by
  apply Sigma.hom_ext
  intro p
  change disjointComparisonInclusion n p.1 p.2 ≫ _ =
    disjointComparisonInclusion n p.1 p.2 ≫ (tgt ≫ disjointComparisonIdentity n)
  rw [← Category.assoc, disjointComparisonInclusion_leftInverse, Category.assoc,
    disjointComposableInclusion_composition, ← Category.assoc,
    productCompositionMap_left_inverse, Category.assoc,
    disjointComparisonInclusion_target_assoc, normalizedDisjointInclusion_identity]

end FLT.Mazur.CyclicCharacteristicAtlas

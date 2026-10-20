/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteGlobalNegation
public import FLT.Mazur.WeierstrassDividedGlobalFiniteStep

/-!
# Finite global negatives retain their exact successor maps

The local successor equivariance and the unchanged infinity formula prove
compatibility on the invariant cover of the entire source. No exceptional
components or original structure morphisms are discarded.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "M" => finiteGlobalModel hπ data j hj
local notation "c" => finiteGlobalContraction hπ data j hj
local notation "i" => finiteNegationInclusion hπ data j hj
local notation "e" => finiteNegationDomainIso hπ data j hj

local notation "C" => finiteNegationCover hπ data j hj

/-- The global negative restricts to the entire finite local negative. -/
@[reassoc] theorem finiteLocalChart_negation :
    finiteLocalChart hπ data j hj ≫ finiteGlobalNegation hπ data j hj =
      (finiteWholeNegationIso hπ data j hj).hom ≫ finiteLocalChart hπ data j hj :=
  finiteNegationInclusion_negation hπ data j hj false

/-- The complete invariant infinity neighborhood retains its original negative. -/
@[reassoc] theorem finiteInfinityNeighborhood_negation :
    infinityNegationInclusion W ≫ finiteInfinityChart hπ data j hj ≫
        finiteGlobalNegation hπ data j hj =
      (WeierstrassGlobalModification.infinityNegationIso W).hom ≫
        infinityNegationInclusion W ≫ finiteInfinityChart hπ data j hj := by
  simpa only [finiteNegationInclusion, finiteNegationDomainIso, Category.assoc] using
    finiteNegationInclusion_negation hπ data j hj true

/-- Every actual global successor commutes with the constructed entire-model negatives. -/
@[reassoc] theorem finiteGlobalNegation_step (hnext : j + 1 ≤ n) :
    finiteGlobalNegation hπ data (j + 1) hnext ≫ finiteGlobalStep hπ data j hnext =
      finiteGlobalStep hπ data j hnext ≫
        finiteGlobalNegation hπ data j (Nat.le_of_succ_le hnext) := by
  apply (finiteNegationCover hπ data (j + 1) hnext).hom_ext
  intro b
  cases b
  · change finiteLocalChart hπ data (j + 1) hnext ≫ _ =
      finiteLocalChart hπ data (j + 1) hnext ≫ _
    rw [finiteLocalChart_negation_assoc, finiteGlobalStep_local,
      finiteGlobalStep_local_assoc, finiteLocalChart_negation,
      finiteWholeNegationIso_step_assoc]
  · change (infinityNegationInclusion W ≫ finiteInfinityChart hπ data (j + 1) hnext) ≫ _ =
      (infinityNegationInclusion W ≫ finiteInfinityChart hπ data (j + 1) hnext) ≫ _
    simp only [Category.assoc]
    rw [finiteInfinityNeighborhood_negation_assoc, finiteGlobalStep_infinity,
      finiteGlobalStep_infinity_assoc, finiteInfinityNeighborhood_negation]

end FLT.Mazur.WeierstrassDividedDepth

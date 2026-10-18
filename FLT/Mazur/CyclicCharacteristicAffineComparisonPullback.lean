/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineComparisonScheme
public import FLT.Mazur.CyclicCharacteristicAffineEquationPullback
public import FLT.Mazur.WeierstrassComparisonPresentationBaseChange

/-!
# Actual comparison schemes on affine chart refinements

Refining an affine chart product gives the geometric pullback of its full
comparison scheme. The two projections retain the base and comparison maps.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open WeierstrassChangeParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] comparisonPresentationBaseChangeIso
variable (n : ℕ) [NeZero n] {A B : Type} [CommRing A] [CommRing B]
  (b c : Bool) (q : Spec (.of A) ⟶ normalizedLocus n b)
  (r : Spec (.of A) ⟶ normalizedLocus n c) (f : A →+* B)
local notation "k" => Spec.map (CommRingCat.ofHom f)
local notation "s" => affineComparisonStructure n b c q r
local notation "s'" => affineComparisonStructure n b c (k ≫ q) (k ≫ r)

/-- The refined full comparison scheme is the actual scheme pullback. -/
def affineComparisonPullbackIso : affineComparisonScheme n b c (k ≫ q) (k ≫ r) ≅
    pullback k s :=
  comparisonPresentationBaseChangeIso (affineEquation n b q) (affineEquation n c r)
    (affineEquation n b (k ≫ q)) (affineEquation n c (k ≫ r)) f
    (affineEquation_pullback n b q f) (affineEquation_pullback n c r f)

/-- The refined chart-product base map is unchanged by the pullback identification. -/
@[reassoc] theorem affineComparisonPullbackIso_fst :
    (affineComparisonPullbackIso n b c q r f).hom ≫ pullback.fst _ _ = s' :=
  comparisonPresentationBaseChangeIso_structure _ _ _ _ _ _ _

/-- The actual overlap map to the original comparison scheme. -/
def affineComparisonRefinement : affineComparisonScheme n b c (k ≫ q) (k ≫ r) ⟶
    affineComparisonScheme n b c q r :=
  (affineComparisonPullbackIso n b c q r f).hom ≫ pullback.snd _ _

/-- Refinement retains the entire original chart-product base square. -/
@[reassoc] theorem affineComparisonRefinement_structure :
    affineComparisonRefinement n b c q r f ≫ s = s' ≫ k := by
  rw [affineComparisonRefinement, Category.assoc, ← pullback.condition,
    ← Category.assoc, affineComparisonPullbackIso_fst]

end FLT.Mazur.CyclicCharacteristicAtlas

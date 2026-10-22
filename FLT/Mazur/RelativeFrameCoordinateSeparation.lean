/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameTestSections
public import FLT.Mazur.SchemeAffineEquationIdeal
public import Mathlib.CategoryTheory.EquivalenceRelation

/-!
# Original coefficient separation of geometric frame coordinates

Joint monicity of the two relation endpoints makes distinct frame coordinates
unequal on every nonempty test. On affine tests, their original coefficient
differences therefore generate the unit ideal, including over nonreduced rings.
No completeness, rank hypothesis, or scalar decomposition is required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S T Z : Scheme.{0}} (E : Over S) [IsSeparated E.hom]
  (I : Type) [Fintype I] {b : T ⟶ S}
  (a : Over.mk b ⟶ distinctScheme E I) (h : E.left ⟶ Z)
  [JointlyMono₂ E.hom h]
set_option quotPrecheck false
local notation "s" i:max => testSection E I a i
local notation "l" i:max => s i ≫ pullback.fst E.hom b ≫ h

/-- Distinct second endpoints have empty full scheme-theoretic equalizer. -/
theorem frameCoordinate_equalizer_isEmpty (i j : I) (hij : i ≠ j) :
    IsEmpty (equalizer (l i) (l j) : Scheme) := by
  let v := equalizer.ι (l i) (l j)
  have hs : v ≫ s i = v ≫ s j := by
    apply pullback.hom_ext
    · apply JointlyMono₂.right_cancellation (p₁ := E.hom) (p₂ := h)
      · simp only [Category.assoc, pullback.condition,
          testSection_snd_assoc]
      · simpa only [Category.assoc] using equalizer.condition (l i) (l j)
    · simp only [Category.assoc, testSection_snd, Category.comp_id]
  refine ⟨fun z ↦ ?_⟩
  have hz : (s i) (v z) = (s j) (v z) := congrArg (fun f ↦ f z) hs
  exact Set.disjoint_left.mp (testSection_disjoint E I a i j hij)
    ⟨v z, rfl⟩ ⟨v z, hz.symm⟩

variable [IsAffine T] [IsAffine Z]

/-- The full original endpoint differences generate one for distinct coordinates. -/
theorem frameCoordinate_differenceIdeal_eq_top (i j : I) (hij : i ≠ j) :
    FiniteCoefficientDifference.differenceIdeal (l i).appTop.hom (l j).appTop.hom = ⊤ := by
  let _ := frameCoordinate_equalizer_isEmpty E I a h i j hij
  change SchemeAffineEquationIdeal.equations (l i) (l j) = ⊤
  rw [← SchemeAffineEquationIdeal.scalar_kernel_eq (l i) (l j)]
  have he := congrArg (fun K : T.IdealSheafData ↦ K.ideal ⟨⊤, isAffineOpen_top T⟩)
    (Scheme.ker_eq_top_of_isEmpty (equalizer.ι (l i) (l j)))
  simpa only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_top, Pi.top_apply] using he

end FLT.Mazur.RelativeOrderedTuples

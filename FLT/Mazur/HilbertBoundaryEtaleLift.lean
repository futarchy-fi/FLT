/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryThickeningNilpotence
public import FLT.Mazur.EtaleNilpotentOverLift

/-!
# Nonaffine etale lifts along the original boundary tower

Every etale target over the unchanged coefficient scheme has unique lifts
along boundary transitions. The lifts satisfy actual scheme tower laws.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
omit [Etale V.hom]
local notation "B" n:max => originalThickenedSource f hL d V c k n
local notation "j" h:max => originalThickenedTransition f hL d V c k h
variable {Y Z : Over (Spec (.of R))} (g : Y ⟶ Z) [Etale g.left]

/-- Whole etale targets, without affine hypotheses, lift along each original transition. -/
theorem originalThickenedTransition_etale_over_lift {m n : ℕ} (h : m ≤ n)
    (a : B m ⟶ Y) (v : B n ⟶ Z) (ha : j h ≫ v = a ≫ g) :
    ∃! b : B n ⟶ Y, j h ≫ b = a ∧ b ≫ g = v :=
  EtaleNilpotentOverLift.existsUnique_lift (j h)
    (originalThickenedTransition_nilpotent f hL d V c k h) g a v ha

/-- The canonical whole lift across a boundary transition, over the original base. -/
def originalThickenedEtaleLift {m n : ℕ} (h : m ≤ n)
    (a : B m ⟶ Y) (v : B n ⟶ Z) (ha : j h ≫ v = a ≫ g) : B n ⟶ Y :=
  EtaleNilpotentOverLift.lift (j h)
    (originalThickenedTransition_nilpotent f hL d V c k h) g a v ha

/-- Restriction retains the complete given lower-order morphism. -/
@[reassoc]
theorem originalThickenedEtaleLift_restrict {m n : ℕ} (h : m ≤ n)
    (a : B m ⟶ Y) (v : B n ⟶ Z) (ha) :
    j h ≫ originalThickenedEtaleLift f hL d V c k g h a v ha = a :=
  EtaleNilpotentOverLift.inclusion_lift _ _ _ _ _ _

/-- The whole coefficient morphism on the higher order is retained. -/
@[reassoc]
theorem originalThickenedEtaleLift_base {m n : ℕ} (h : m ≤ n)
    (a : B m ⟶ Y) (v : B n ⟶ Z) (ha) :
    originalThickenedEtaleLift f hL d V c k g h a v ha ≫ g = v :=
  EtaleNilpotentOverLift.lift_base _ _ _ _ _ _

/-- Direct lifting equals successive lifting through an intermediate infinitesimal order. -/
theorem originalThickenedEtaleLift_comp {l m n : ℕ} (h₁ : l ≤ m) (h₂ : m ≤ n)
    (a : B l ⟶ Y) (v : B n ⟶ Z) (ha : j(h₁.trans h₂) ≫ v = a ≫ g) :
    originalThickenedEtaleLift f hL d V c k g (h₁.trans h₂) a v ha =
      originalThickenedEtaleLift f hL d V c k g h₂
        (originalThickenedEtaleLift f hL d V c k g h₁ a (j h₂ ≫ v) (by
          rw [← Category.assoc, originalThickenedTransition_comp, ha])) v
        (by rw [originalThickenedEtaleLift_base]) := by
  apply EtaleNilpotentOverLift.lift_eq
  · rw [← originalThickenedTransition_comp f hL d V c k h₁ h₂, Category.assoc,
      originalThickenedEtaleLift_restrict, originalThickenedEtaleLift_restrict]
  · exact originalThickenedEtaleLift_base f hL d V c k g h₂ _ v _

/-- Lifting through an equal order is the original map. -/
theorem originalThickenedEtaleLift_refl (n : ℕ) (a : B n ⟶ Y) :
    originalThickenedEtaleLift f hL d V c k g (le_refl n) a (a ≫ g)
      (by rw [originalThickenedTransition_refl, Category.id_comp]) = a := by
  apply EtaleNilpotentOverLift.lift_eq
  · rw [originalThickenedTransition_refl, Category.id_comp]
  · rfl

end FLT.Mazur.HilbertChart.AffineRestriction

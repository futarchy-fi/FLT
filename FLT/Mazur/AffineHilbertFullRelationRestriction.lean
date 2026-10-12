/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertRelationOperations

/-!
# The original full relation on a restricted Hilbert source

The equal-class relation on a source restriction is the actual two-endpoint
pullback of the original full relation. All original arrows with both endpoints
in the restriction lift, including arrows with independent translation bases.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "p" => variableChartRelationFst f hL d V c
local notation "q" => variableChartRelationSnd f hL d V c
local notation "r" => fst f hL d V c k
local notation "s" => snd f hL d V c k

/-- Forgetting the source restriction retains the actual original full relation arrow. -/
def toFullRelation : relation f hL d V c k ⟶ variableChartRelation f hL d V c :=
  variableChartRelationLift f hL d V c (r ≫ k) (s ≫ k) (by
    simpa only [sectionAt, op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using
      equal_class f hL d V c k)

@[reassoc]
theorem toFullRelation_fst : toFullRelation f hL d V c k ≫ p = r ≫ k :=
  variableChartRelationLift_fst f hL d V c _ _ _

@[reassoc]
theorem toFullRelation_snd : toFullRelation f hL d V c k ≫ q = s ≫ k :=
  variableChartRelationLift_snd f hL d V c _ _ _

/-- Restrict the first endpoint of the unchanged original relation. -/
def fullFirstRestriction : Over (Spec (.of R)) := pullback p k

/-- Restrict the second endpoint after the first, retaining the original relation scheme. -/
def fullDoubleRestriction : Over (Spec (.of R)) := pullback (pullback.fst p k ≫ q) k

/-- The full two-endpoint restriction remembers its first source coordinate. -/
def fullDoubleFst : fullDoubleRestriction f hL d V c k ⟶ A :=
  pullback.fst (pullback.fst p k ≫ q) k ≫ pullback.snd p k

/-- Its second source coordinate is independent of the first one. -/
def fullDoubleSnd : fullDoubleRestriction f hL d V c k ⟶ A :=
  pullback.snd (pullback.fst p k ≫ q) k

/-- The unchanged original arrow underlying the double restriction. -/
def fullDoubleArrow : fullDoubleRestriction f hL d V c k ⟶
    variableChartRelation f hL d V c :=
  pullback.fst (pullback.fst p k ≫ q) k ≫ pullback.fst p k

@[reassoc]
theorem fullDoubleArrow_fst : fullDoubleArrow f hL d V c k ≫ p =
    fullDoubleFst f hL d V c k ≫ k := by
  simp only [fullDoubleArrow, fullDoubleFst, Category.assoc, pullback.condition]

@[reassoc]
theorem fullDoubleArrow_snd : fullDoubleArrow f hL d V c k ≫ q =
    fullDoubleSnd f hL d V c k ≫ k := by
  exact pullback.condition (f := pullback.fst p k ≫ q) (g := k)

/-- An original arrow with lifted endpoints determines the restricted equal-class arrow. -/
def fromFullDouble : fullDoubleRestriction f hL d V c k ⟶ relation f hL d V c k :=
  arrow f hL d V c k (fullDoubleFst f hL d V c k) (fullDoubleSnd f hL d V c k) (by
    have h := congrArg ((relativeFppfSheaf f).obj.map (fullDoubleArrow f hL d V c k).op)
      (variableChartRelation_class f hL d V c)
    simpa only [sectionAt, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      fullDoubleArrow_fst, fullDoubleArrow_snd] using h)

@[reassoc]
theorem fromFullDouble_fst : fromFullDouble f hL d V c k ≫ r =
    fullDoubleFst f hL d V c k := arrow_fst f hL d V c k _ _ _

@[reassoc]
theorem fromFullDouble_snd : fromFullDouble f hL d V c k ≫ s =
    fullDoubleSnd f hL d V c k := arrow_snd f hL d V c k _ _ _

/-- The restricted relation maps to the actual two-endpoint pullback. -/
def toFullDouble : relation f hL d V c k ⟶ fullDoubleRestriction f hL d V c k :=
  pullback.lift (pullback.lift (toFullRelation f hL d V c k) r
    (toFullRelation_fst f hL d V c k)) s (by
      rw [pullback.lift_fst_assoc, toFullRelation_snd])

@[reassoc]
theorem toFullDouble_fst : toFullDouble f hL d V c k ≫ fullDoubleFst f hL d V c k = r := by
  simp only [toFullDouble, fullDoubleFst, pullback.lift_fst_assoc, pullback.lift_snd]

@[reassoc]
theorem toFullDouble_snd : toFullDouble f hL d V c k ≫ fullDoubleSnd f hL d V c k = s :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem fromFullDouble_original : fromFullDouble f hL d V c k ≫
    toFullRelation f hL d V c k = fullDoubleArrow f hL d V c k := by
  apply variableChartRelation_hom_ext f hL d V c
  · rw [Category.assoc, toFullRelation_fst, ← Category.assoc,
      fromFullDouble_fst, fullDoubleArrow_fst]
  · rw [Category.assoc, toFullRelation_snd, ← Category.assoc,
      fromFullDouble_snd, fullDoubleArrow_snd]

/-- The equal-class relation is exactly the original full relation restricted at both endpoints. -/
def fullDoubleIso : relation f hL d V c k ≅ fullDoubleRestriction f hL d V c k where
  hom := toFullDouble f hL d V c k
  inv := fromFullDouble f hL d V c k
  hom_inv_id := by
    apply hom_ext f hL d V c k
    · rw [Category.assoc, fromFullDouble_fst, toFullDouble_fst, Category.id_comp]
    · rw [Category.assoc, fromFullDouble_snd, toFullDouble_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [toFullDouble, Category.assoc, pullback.lift_fst, Category.id_comp]
        exact fromFullDouble_original f hL d V c k
      · simp only [toFullDouble, Category.assoc, pullback.lift_fst_assoc,
          pullback.lift_snd, Category.id_comp]
        exact fromFullDouble_fst f hL d V c k
    · simp only [toFullDouble, Category.assoc, pullback.lift_snd, Category.id_comp]
      exact fromFullDouble_snd f hL d V c k

/-- Every original arrow whose endpoints lift to the source restriction has a restricted lift. -/
theorem original_arrow_lift (a : (variableChartRelation f hL d V c).left) (x y : A.left)
    (hx : (p).left a = k.left x) (hy : (q).left a = k.left y) :
    ∃ b : (relation f hL d V c k).left, (r).left b = x ∧ (s).left b = y := by
  obtain ⟨b, hb, hx'⟩ := Scheme.exists_preimage_of_isPullback
    ((IsPullback.of_hasPullback p k).map (Over.forget _)) a x hx
  have hy' : (pullback.fst p k ≫ q).left b = k.left y :=
    (congrArg (q).left hb).trans hy
  obtain ⟨t, ht, hy''⟩ := Scheme.exists_preimage_of_isPullback
    ((IsPullback.of_hasPullback (pullback.fst p k ≫ q) k).map (Over.forget _)) b y hy'
  refine ⟨(fromFullDouble f hL d V c k).left t, ?_, ?_⟩
  · have h := congrArg (fun z ↦ z.left t) (fromFullDouble_fst f hL d V c k)
    exact h.trans ((congrArg (pullback.snd p k).left ht).trans hx')
  · exact (congrArg (fun z ↦ z.left t) (fromFullDouble_snd f hL d V c k)).trans hy''

end FLT.Mazur.HilbertChart.AffineRestriction

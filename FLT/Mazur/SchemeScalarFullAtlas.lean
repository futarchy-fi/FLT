/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfRelationDescent
public import FLT.Mazur.SchemeScalarRelationTransition

/-!
# Covering the entire original scalar-test source

Base change the original covering atlas over the full source pullback.
The family covers every source point, with no chart-completeness hypothesis.
Its full mixed relation equations recover the actual scalar-test equalizer.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarRelationPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X D S Y : Scheme.{0}} (p q : D ⟶ X) (s : X ⟶ S)
  (hs : p ≫ s = q ≫ s) (b : Y ⟶ S)
  (C : Scheme.Cover.{0} Scheme.fppfPrecoverage X)

/-- The original atlas pulled back over the entire scalar-test source. -/
abbrev fullAtlas : (testSource s b).Cover Scheme.fppfPrecoverage :=
  C.pullback₁ (pullback.fst s b)

/-- Scalar base change keeps the original finite indexing family. -/
instance fullAtlasFintype [Fintype C.I₀] : Fintype (fullAtlas s b C).I₀ :=
  inferInstanceAs (Fintype C.I₀)

/-- The full source, including points outside any chosen complete chart, is covered. -/
theorem fullAtlas_covers (x : testSource s b) :
    ∃ a : C.I₀, ∃ z : (fullAtlas s b C).X a, (fullAtlas s b C).f a z = x :=
  by
    let V : (testSource s b).Cover
        (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := fullAtlas s b C
    exact V.exists_eq x

/-- Exact source coefficients are detected on this actual full cover. -/
theorem fullAtlas_sections_ext {u v : Γ(testSource s b, ⊤)}
    (h : ∀ a : C.I₀, ((fullAtlas s b C).f a).appTop u =
      ((fullAtlas s b C).f a).appTop v) : u = v :=
  SchemeFppfFamily.cover_sections_ext (fullAtlas s b C) h

variable (r : X ⟶ D) (hrp : r ≫ p = 𝟙 X) (hrq : r ≫ q = 𝟙 X)

/-- Reflexivity survives scalar base change on the full relation. -/
def testReflexivity : testSource s b ⟶ testRelation p s b :=
  pullback.lift (pullback.fst s b ≫ r) (pullback.snd s b)
    (by simp only [Category.assoc, ← Category.assoc r p s, hrp, Category.id_comp,
      pullback.condition])

/-- The first pulled endpoint of reflexivity is the identity on the full source. -/
theorem testReflexivity_first : testReflexivity p s b r hrp ≫ testFirst p s b =
    𝟙 (testSource s b) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, testFirst_fst, testReflexivity, pullback.lift_fst_assoc,
      hrp, Category.comp_id, Category.id_comp]
  · simp only [Category.assoc, testFirst, testReflexivity, pullback.lift_snd,
      Category.id_comp]

include hrq in
/-- Reflexivity also retains the independent second pulled endpoint. -/
theorem testReflexivity_second : testReflexivity p s b r hrp ≫ testSecond p q s hs b =
    𝟙 (testSource s b) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, testSecond_fst, testReflexivity, pullback.lift_fst_assoc,
      hrq, Category.comp_id, Category.id_comp]
  · simp only [Category.assoc, testSecond, testReflexivity, pullback.lift_snd,
      Category.id_comp]

include r hrp hrq in
/-- Compatible full-atlas coefficients descend to the actual unreduced test equalizer. -/
theorem fullAtlas_invariants_descend (v : ∀ a, Γ((fullAtlas s b C).X a, ⊤))
    (hv : SchemeFppfRelationDescent.Compatible
      (testFirst p s b) (testSecond p q s hs b) (fullAtlas s b C) v) :
    ∃! t : testInvariants p q s hs b,
      ∀ a, ((fullAtlas s b C).f a).appTop t.val = v a := by
  obtain ⟨t, ht, hu⟩ := SchemeFppfRelationDescent.compatible_existsUnique
    (testFirst p s b) (testSecond p q s hs b) (fullAtlas s b C)
    (testReflexivity p s b r hrp) (testReflexivity_first p s b r hrp)
    (testReflexivity_second p q s hs b r hrp hrq) v hv
  exact ⟨t, fun a ↦ congrFun ht a, fun z hz ↦ hu z (funext hz)⟩

end FLT.Mazur.SchemeScalarRelationPullback

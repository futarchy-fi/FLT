/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeTupleCompletenessLocus
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Disjoint original frame sections over arbitrary test schemes

A scheme-valued distinct frame supplies disjoint open sections of the entire
original pullback. Neither the test scheme nor its coefficients are reduced.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (I : Type) [Fintype I] {T : Scheme} {b : T ⟶ S}
  (t : Over.mk b ⟶ distinctScheme E I)

/-- The actual coordinate section of the whole original pullback over any test. -/
def testSection (i : I) : T ⟶ pullback E.hom b :=
  pullback.lift (t ≫ distinctCoordinate E I i).left (𝟙 _) (by
    rw [Category.id_comp]
    exact (t ≫ distinctCoordinate E I i).w)

omit [Etale E.hom] in
@[reassoc (attr := simp)] theorem testSection_fst (i : I) :
    testSection E I t i ≫ pullback.fst E.hom b =
      (t ≫ distinctCoordinate E I i).left := pullback.lift_fst _ _ _

omit [Etale E.hom] in
@[reassoc (attr := simp)] theorem testSection_snd (i : I) :
    testSection E I t i ≫ pullback.snd E.hom b = 𝟙 _ := pullback.lift_snd _ _ _

/-- Every coordinate is open even for a nonreduced test scheme. -/
instance testSection_isOpenImmersion (i : I) : IsOpenImmersion (testSection E I t i) :=
  UnramifiedSectionImmersion.isOpenImmersion (pullback.snd E.hom b) _
    (testSection_snd E I t i)

omit [Etale E.hom] in
/-- Distinct original coordinates have disjoint images over every test scheme. -/
theorem testSection_disjoint (i j : I) (hij : i ≠ j) :
    Disjoint (Set.range (testSection E I t i)) (Set.range (testSection E I t j)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  let si := testSection E I t i
  let sj := testSection E I t j
  have hx : x ∈ Set.range (pullback.fst si sj) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨y, hy⟩
  obtain ⟨z, _⟩ := hx
  let _ : Nonempty (Over.mk (pullback.fst si sj ≫ b)).left := ⟨z⟩
  have hp : pullback.fst si sj = pullback.snd si sj := by
    have h := congrArg (fun f ↦ f ≫ pullback.snd E.hom b) (pullback.condition (f := si) (g := sj))
    simpa only [Category.assoc, si, sj, testSection_snd, Category.comp_id] using h
  let v : Over.mk (pullback.fst si sj ≫ b) ⟶ Over.mk b :=
    Over.homMk (pullback.fst si sj)
  apply hij
  apply distinctCoordinate_injective E I (v ≫ t)
  apply Over.OverMorphism.ext
  have h := congrArg (fun f ↦ f ≫ pullback.fst E.hom b) (pullback.condition (f := si) (g := sj))
  simpa only [Category.assoc, si, sj, testSection_fst, ← hp, v,
    Over.comp_left, Over.homMk_left] using h

/-- All coordinates assemble into an open immersion into the full original pullback. -/
def testComparison : (∐ fun _ : I ↦ T) ⟶ pullback E.hom b :=
  Sigma.desc (testSection E I t)

omit [Etale E.hom] in
@[reassoc] theorem testComparison_component (i : I) :
    Sigma.ι (fun _ : I ↦ T) i ≫ testComparison E I t = testSection E I t i :=
  Sigma.ι_comp_desc _ _

instance testComparison_isOpenImmersion : IsOpenImmersion (testComparison E I t) :=
  AlgebraicGeometry.isOpenImmersion_sigmaDesc _ (testSection E I t)
    (testSection_disjoint E I t)

end FLT.Mazur.RelativeOrderedTuples

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameTestSplitting
public import FLT.Mazur.SchemeEquationPullback

/-!
# Complete frames split full endpoint equations

The equation imposing the second endpoint on the entire first-source
pullback splits into disjoint coordinate equalizers. The construction works
over arbitrary coefficient schemes and retains their nilpotent structure.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S T Z : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (I : Type) [Fintype I] {b : T ⟶ S}
  (a : Over.mk b ⟶ distinctScheme E I) (h : E.left ⟶ Z) (y : T ⟶ Z)
local notation "f" => pullback.fst E.hom b ≫ h
local notation "g" => pullback.snd E.hom b ≫ y
local notation "s" i:max => testSection E I a i

/-- The full equation for the second endpoint inside the original first-source pullback. -/
abbrev frameEquation := equalizer f g

/-- Each coordinate contributes its own full scheme-theoretic equation. -/
abbrev frameEquationChart (i : I) := equalizer (s i ≫ f) (s i ≫ g)

/-- The coordinate equation embeds into the full original endpoint equation. -/
def frameEquationMap (i : I) : frameEquationChart E I a h y i ⟶ frameEquation E (b := b) h y :=
  SchemeEquationPullback.map f g (s i)

omit [Etale E.hom] in
/-- Equation charts retain their original coordinate sections exactly. -/
@[reassoc] theorem frameEquationMap_ι (i : I) :
    frameEquationMap E I a h y i ≫ equalizer.ι f g =
      equalizer.ι (s i ≫ f) (s i ≫ g) ≫ s i :=
  SchemeEquationPullback.map_ι f g (s i)

/-- Every coordinate equation is an open chart of the full equation scheme. -/
instance frameEquationMap_isOpenImmersion (i : I) :
    IsOpenImmersion (frameEquationMap E I a h y i) :=
  inferInstanceAs (IsOpenImmersion (SchemeEquationPullback.map f g (s i)))

omit [Etale E.hom] in
/-- Distinct coordinate equations have disjoint images, including over nonreduced tests. -/
theorem frameEquationMap_disjoint (i j : I) (hij : i ≠ j) :
    Disjoint (Set.range (frameEquationMap E I a h y i))
      (Set.range (frameEquationMap E I a h y j)) := by
  change Disjoint (Set.range (SchemeEquationPullback.map f g (s i)))
    (Set.range (SchemeEquationPullback.map f g (s j)))
  rw [SchemeEquationPullback.range_map, SchemeEquationPullback.range_map]
  exact (testSection_disjoint E I a i j hij).preimage _

/-- Complete frames cover every point of the full endpoint equation. -/
theorem frameEquationMap_cover (ha : Set.range a.left ⊆ completeLocus E I)
    (z : frameEquation E (b := b) h y) :
    ∃ i : I, z ∈ Set.range (frameEquationMap E I a h y i) := by
  obtain ⟨i, hi⟩ := testSection_cover_of_complete E I a ha (equalizer.ι f g z)
  refine ⟨i, ?_⟩
  exact (SchemeEquationPullback.range_map f g (s i)).symm ▸ hi

/-- Assemble the actual coordinate equalizers into the entire endpoint equation. -/
def frameEquationComparison :
    (∐ fun i : I ↦ frameEquationChart E I a h y i) ⟶ frameEquation E (b := b) h y :=
  Sigma.desc (frameEquationMap E I a h y)

omit [Etale E.hom] in
/-- The assembled comparison agrees with each actual coordinate chart. -/
@[reassoc] theorem frameEquationComparison_component (i : I) :
    Sigma.ι (fun i : I ↦ frameEquationChart E I a h y i) i ≫
      frameEquationComparison E I a h y = frameEquationMap E I a h y i :=
  Sigma.ι_comp_desc _ _

/-- The coordinate equations form disjoint open subschemes of the full comparison. -/
instance frameEquationComparison_isOpenImmersion :
    IsOpenImmersion (frameEquationComparison E I a h y) :=
  AlgebraicGeometry.isOpenImmersion_sigmaDesc _ (frameEquationMap E I a h y)
    (frameEquationMap_disjoint E I a h y)

/-- Completeness identifies the entire original equation with its coordinate equations. -/
theorem frameEquationComparison_isIso (ha : Set.range a.left ⊆ completeLocus E I) :
    IsIso (frameEquationComparison E I a h y) := by
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  refine ⟨inferInstance, ⟨fun z ↦ ?_⟩⟩
  obtain ⟨i, w, hw⟩ := frameEquationMap_cover E I a h y ha z
  refine ⟨(Sigma.ι (fun i : I ↦ frameEquationChart E I a h y i) i) w, ?_⟩
  exact (congrArg (fun u ↦ u w)
    (frameEquationComparison_component E I a h y i)).trans hw

/-- A full, unreduced endpoint equation splits as the coproduct of coordinate equalizers. -/
def frameEquationIso (ha : Set.range a.left ⊆ completeLocus E I) :
    (∐ fun i : I ↦ frameEquationChart E I a h y i) ≅ frameEquation E (b := b) h y := by
  let _ := frameEquationComparison_isIso E I a h y ha
  exact asIso (frameEquationComparison E I a h y)

end FLT.Mazur.RelativeOrderedTuples

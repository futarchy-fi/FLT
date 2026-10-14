/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationReanchoring
public import FLT.Mazur.SchemeRelationSplitOrbit

/-!
# Complete orbit atlases over the original source

An etale covering seed produces an etale cover of the original parameter
scheme. Reanchoring compares its FULL original relation with the relation
between its independent seeds. No coefficient flatness or openness into a
changed Hilbert parameter scheme is asserted or required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationOrbitAtlas
open SchemeRelationRestriction SchemeRelationSplitOrbit
set_option backward.isDefEq.respectTransparency false
variable {S Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (s : Z ⟶ A.left)
local notation "B" => (pullback q.left s : Scheme)
local notation "r" => pullback.fst q.left s
local notation "π" => pullback.snd q.left s
local notation "b" => SchemeRelationEtaleBranchPropagation.branch p.left q.left s

/-- The complete orbit is a source over the ORIGINAL base. -/
def source : Over S := Over.mk (b ≫ A.hom)

/-- Its actual map to the original source, without any coefficient base change. -/
def toOriginal : source (p := p) (q := q) s ⟶ A := Over.homMk b

/-- Its independent seed coordinate. -/
def seedCoordinate : (source (p := p) (q := q) s).left ⟶ Z := π

/-- The original arrow relates the source map and the full seed map. -/
@[reassoc]
theorem arrow_seed : r ≫ q.left = seedCoordinate (p := p) (q := q) s ≫ s :=
  pullback.condition

include e in
/-- A covering seed makes the complete orbit cover every original parameter point. -/
theorem toOriginal_surjective [Surjective s] :
    Surjective (toOriginal (p := p) (q := q) s).left := by
  constructor
  intro x
  obtain ⟨z, hz⟩ := s.surjective x
  exact ⟨sectionMap e s z, (sectionMap_point e s z).trans hz⟩

instance toOriginal_etale [Etale p.left] [Etale s] :
    Etale (toOriginal (p := p) (q := q) s).left :=
  inferInstanceAs (Etale b)

instance seedCoordinate_etale [Etale q.left] :
    Etale (seedCoordinate (p := p) (q := q) s) := inferInstanceAs (Etale π)

include e in
/-- The other projection covers every seed by reflexivity, even without a covering seed. -/
theorem seedCoordinate_surjective : Surjective (seedCoordinate (p := p) (q := q) s) :=
  projection_surjective e s

/-- The full original relation on the covering orbit has independent source endpoints. -/
def originalRelation : Scheme.{u} := doubleDomain p.left q.left b

/-- The complete seed relation on the SAME orbit, with no equality imposed on seed coordinates. -/
def seedRelation : Scheme.{u} := doubleDomain p.left q.left (r ≫ q.left)

/-- The full original relation is isomorphic to the relation between independent seeds. -/
def fullRelationIso : originalRelation (p := p) (q := q) s ≅
    seedRelation (p := p) (q := q) s := SchemeRelationReanchoring.relationIso e r

@[reassoc]
theorem fullRelationIso_fst : (fullRelationIso e s).hom ≫
    fst p.left q.left (r ≫ q.left) = fst p.left q.left b :=
  SchemeRelationReanchoring.forward_fst e r

@[reassoc]
theorem fullRelationIso_snd : (fullRelationIso e s).hom ≫
    snd p.left q.left (r ≫ q.left) = snd p.left q.left b :=
  SchemeRelationReanchoring.forward_snd e r

include e in
/-- Invariant scheme maps are tested by all seed arrows, including different seeds. -/
theorem invariant_iff {T : Scheme.{u}} (v : B ⟶ T) :
    fst p.left q.left b ≫ v = snd p.left q.left b ≫ v ↔
      fst p.left q.left (r ≫ q.left) ≫ v = snd p.left q.left (r ≫ q.left) ≫ v :=
  SchemeRelationReanchoring.invariant_iff e r v

include e in
/-- The identity seed gives an unconditional cover of the original source. -/
theorem identity_cover [Etale p.left] :
    Etale (toOriginal (p := p) (q := q) (𝟙 A.left)).left ∧
      Surjective (toOriginal (p := p) (q := q) (𝟙 A.left)).left :=
  ⟨inferInstance, toOriginal_surjective e _⟩

end FLT.Mazur.SchemeRelationOrbitAtlas

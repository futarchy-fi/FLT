/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationOrbitAtlas
public import FLT.Mazur.AffineHilbertNestedRestriction
public import FLT.Mazur.AffineHilbertRelationNeighborhoods

/-!
# Full original Picard relations on complete orbit atlases

Covering seeds give actual etale covers of the original parameter source.
The rebuilt ORIGINAL-family Picard relation on this cover is isomorphic to
the relation between independent seed coordinates. No new-ground equality
is imposed, and no openness of the map into Hilbert parameters is claimed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "e" => equivalence f hL d V c k
variable {Z : Scheme} (s : Z ⟶ A.left)
local notation "r" => pullback.fst (Over.Hom.left q) s

/-- Complete orbit parameters over the unchanged original family base. -/
def originalOrbitSource : Over (Spec (.of R)) :=
  SchemeRelationOrbitAtlas.source («p» := p) («q» := q) s

/-- The actual etale atlas map to the original source. -/
def originalOrbitToSource : originalOrbitSource f hL d V c k s ⟶ A :=
  SchemeRelationOrbitAtlas.toOriginal («p» := p) («q» := q) s

/-- An actual ORIGINAL-family parameter map; an etale atlas need not be an open chart. -/
def originalOrbitParameter : originalOrbitSource f hL d V c k s ⟶
    variableHilbertTest f d V := originalOrbitToSource f hL d V c k s ≫ k

local notation "u" => originalOrbitToSource f hL d V c k s
local notation "l" => originalOrbitParameter f hL d V c k s
local notation "p'" => fst f hL d V c l
local notation "q'" => snd f hL d V c l

/-- The original Picard relation is the full relation between independent seed coordinates. -/
def originalOrbitSeedRelationIso : (relation f hL d V c l).left ≅
    SchemeRelationOrbitAtlas.seedRelation («p» := p) («q» := q) s :=
  nestedSchemeDoubleIso f hL d V c k u ≪≫ SchemeRelationOrbitAtlas.fullRelationIso e s

/-- The first endpoint of the original-family full relation survives the comparison. -/
@[reassoc]
theorem originalOrbitSeedRelationIso_fst :
    (originalOrbitSeedRelationIso f hL d V c k s).hom ≫
      SchemeRelationRestriction.fst (p).left (q).left (r ≫ (q).left) = (p').left := by
  dsimp only [originalOrbitSeedRelationIso, Iso.trans_hom]
  rw [Category.assoc, SchemeRelationOrbitAtlas.fullRelationIso_fst]
  change (nestedSchemeDoubleIso f hL d V c k u).hom ≫
    SchemeRelationRestriction.fst (p).left (q).left (u).left = (p').left
  dsimp only [nestedSchemeDoubleIso, Iso.trans_hom, Functor.mapIso_hom,
    SchemeRelationRestriction.overDoubleIso]
  rw [Category.assoc, SchemeRelationRestriction.overToDouble_fst]
  exact congrArg Over.Hom.left (nestedToFullDouble_fst f hL d V c k u)

/-- The second endpoint remains independent, including its entire seed morphism. -/
@[reassoc]
theorem originalOrbitSeedRelationIso_snd :
    (originalOrbitSeedRelationIso f hL d V c k s).hom ≫
      SchemeRelationRestriction.snd (p).left (q).left (r ≫ (q).left) = (q').left := by
  dsimp only [originalOrbitSeedRelationIso, Iso.trans_hom]
  rw [Category.assoc, SchemeRelationOrbitAtlas.fullRelationIso_snd]
  change (nestedSchemeDoubleIso f hL d V c k u).hom ≫
    SchemeRelationRestriction.snd (p).left (q).left (u).left = (q').left
  dsimp only [nestedSchemeDoubleIso, Iso.trans_hom, Functor.mapIso_hom,
    SchemeRelationRestriction.overDoubleIso]
  rw [Category.assoc, SchemeRelationRestriction.overToDouble_snd]
  exact congrArg Over.Hom.left (nestedToFullDouble_snd f hL d V c k u)

/-- The actual original source is covered whenever the seed covers it. -/
theorem originalOrbitToSource_surjective [Surjective s] : Surjective (u).left :=
  SchemeRelationOrbitAtlas.toOriginal_surjective e s

variable [Etale V.hom] [IsOpenImmersion k.left]

instance originalOrbitToSource_etale [Etale s] : Etale (u).left :=
  inferInstanceAs (Etale (SchemeRelationOrbitAtlas.toOriginal («p» := p) («q» := q) s).left)

/-- The parameter map is etale for an etale seed, on the ORIGINAL family. -/
instance originalOrbitParameter_etale [Etale s] : Etale (l).left := by
  change Etale ((u).left ≫ k.left)
  infer_instance

/-- Identity seeds construct a genuine etale covering atlas of every original selected source. -/
theorem originalOrbit_identity_cover :
    Etale (originalOrbitToSource f hL d V c k (𝟙 A.left)).left ∧
      Surjective (originalOrbitToSource f hL d V c k (𝟙 A.left)).left :=
  ⟨inferInstance, originalOrbitToSource_surjective f hL d V c k _⟩

/-- Every original point is hit without an unramified coefficient or generic-coverage premise. -/
theorem originalOrbit_identity_point (x : A.left) :
    ∃ z : (originalOrbitSource f hL d V c k (𝟙 A.left)).left,
      (originalOrbitToSource f hL d V c k (𝟙 A.left)).left z = x ∧
      (originalOrbitParameter f hL d V c k (𝟙 A.left)).left z = k.left x := by
  obtain ⟨z, hz⟩ := (originalOrbit_identity_cover f hL d V c k).2.1 x
  exact ⟨z, hz, congrArg k.left hz⟩

end FLT.Mazur.HilbertChart.AffineRestriction

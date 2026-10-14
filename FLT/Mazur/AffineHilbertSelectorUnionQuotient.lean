/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertNestedKernel
public import FLT.Mazur.AffineHilbertRelationNeighborhoods
public import FLT.Mazur.SchemeRelationOpenSelectorInvariant

/-!
# Assembled original proper-family quotients on the selector union

Independent original representatives construct a quotient on their invariant
open union. Its full kernel is the freshly recomputed original Hilbert relation,
and its invariant locally ringed space is the constructed quotient scheme.
No claim that this union covers the entire parameter scheme is made.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "e" => equivalence f hL d V c k

/-- The actual invariant open union inside the original parameter source. -/
def selectorUnionSource : Over (Spec (.of R)) :=
  SchemeRelationOpenSelector.relativeSource («p» := p) («q» := q)

/-- Its literal inclusion in the original source retains the unchanged ground. -/
def selectorUnionInclusion : selectorUnionSource f hL d V c k ⟶ A :=
  SchemeRelationOpenSelector.relativeSourceInclusion («p» := p) («q» := q)

/-- The union is an original proper-family Hilbert selection. -/
def selectorUnionParameter : selectorUnionSource f hL d V c k ⟶ variableHilbertTest f d V :=
  selectorUnionInclusion f hL d V c k ≫ k

/-- The quotient scheme is constructed by gluing independent original selector charts. -/
def selectorUnionTarget : Over (Spec (.of R)) := SchemeRelationOpenSelector.relativeGlued e

/-- The constructed projection is a morphism over the original proper-family base. -/
def selectorUnionProjection : selectorUnionSource f hL d V c k ⟶
    selectorUnionTarget f hL d V c k := SchemeRelationOpenSelector.relativeProjection e

/-- The assembled proper-family projection is an etale surjection onto its entire target. -/
theorem selectorUnionProjection_cover :
    Etale (selectorUnionProjection f hL d V c k).left ∧
      Surjective (selectorUnionProjection f hL d V c k).left :=
  ⟨SchemeRelationOpenSelector.projection_etale e,
    SchemeRelationOpenSelector.projection_surjective e⟩

/-- The freshly recomputed ORIGINAL Hilbert relation is the full constructed scheme kernel. -/
theorem selectorUnionProjection_isPullback :
    IsPullback (fst f hL d V c (selectorUnionParameter f hL d V c k)).left
      (snd f hL d V c (selectorUnionParameter f hL d V c k)).left
      (selectorUnionProjection f hL d V c k).left
      (selectorUnionProjection f hL d V c k).left :=
  nested_isPullback f hL d V c k (selectorUnionInclusion f hL d V c k) _
    (SchemeRelationOpenSelector.projection_isPullback e)

/-- The original relative relation also has the full kernel over the unchanged base. -/
theorem selectorUnionProjection_relative_isPullback :
    IsPullback (fst f hL d V c (selectorUnionParameter f hL d V c k))
      (snd f hL d V c (selectorUnionParameter f hL d V c k))
      (selectorUnionProjection f hL d V c k) (selectorUnionProjection f hL d V c k) :=
  IsPullback.of_map_of_faithful (Over.forget _) (selectorUnionProjection_isPullback f hL d V c k)

local notation "e'" => equivalence f hL d V c (selectorUnionParameter f hL d V c k)

/-- The original invariant locally ringed quotient is the actual assembled scheme. -/
def selectorUnionInvariantIso : invariantLocallyRingedSpace e' ≅
    (selectorUnionTarget f hL d V c k).left.toLocallyRingedSpace := by
  obtain ⟨he, hs⟩ := selectorUnionProjection_cover f hL d V c k
  let _ := he
  let _ := hs
  exact fppfInvariantQuotientIso e' (selectorUnionProjection f hL d V c k)
    (selectorUnionProjection_relative_isPullback f hL d V c k)

/-- The full structure-sheaf comparison preserves the original source projection. -/
@[reassoc]
theorem selectorUnionInvariantIso_projection : invariantLocallyRingedProjection e' ≫
    (selectorUnionInvariantIso f hL d V c k).hom =
      (selectorUnionProjection f hL d V c k).left.toLRSHom := by
  obtain ⟨he, hs⟩ := selectorUnionProjection_cover f hL d V c k
  let _ := he
  let _ := hs
  exact fppfInvariantQuotientIso_projection e' (selectorUnionProjection f hL d V c k)
    (selectorUnionProjection_relative_isPullback f hL d V c k)

/-- The invariant quotient retains the ORIGINAL proper-family ground morphism. -/
theorem selectorUnionInvariantIso_ground : (selectorUnionInvariantIso f hL d V c k).hom ≫
    (selectorUnionTarget f hL d V c k).hom.toLRSHom = invariantLocallyRingedBaseMap e' := by
  obtain ⟨he, hs⟩ := selectorUnionProjection_cover f hL d V c k
  let _ := he
  let _ := hs
  exact fppfInvariantQuotientIso_baseMap e' (selectorUnionProjection f hL d V c k)
    (selectorUnionProjection_relative_isPullback f hL d V c k)

end FLT.Mazur.HilbertChart.AffineRestriction

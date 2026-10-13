/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertIdentityGroundOriginalBaseSquare
public import FLT.Mazur.OrderedHilbertIdentityOriginalSection

/-!
# The original Picard source and the quotient source have the same base

Compare both coefficient morphisms on each unchanged affine component, then
use the actual scheme coproduct to identify their assembled base maps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertIdentityOriginalBaseSquare
open HilbertChart CartierAbel SchemePicard FCurve RelativeRelationOrbit
open OrderedHilbertIdentityOriginalSection
open OrderedHilbertAffineEtaleTestCover OrderedHilbertFaithfulTestCover AffineRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
local notation "T" => smoothHilbertSource f
local notation "s" => smoothHilbertSourceSection f hL
local notation "E" => fun x ↦ Sigma.fst (Sigma.snd (chartData f hL T s x))
local notation "d" => fun x ↦ Prod.snd (Sigma.fst (chartData f hL T s x))
local notation "c" => fun x ↦ chartClass f hL T s x
local notation "p" => fun x ↦ retainedParameter f hL x
local notation "k" => fun x ↦ AffineParameterNeighborhood.chart f (d x) (E x) (p x)
local notation "Q" => OrderedHilbertIdentityQuotientCover.source f hL
local notation "e" => smoothHilbertEquivalenceRelation f hL

/-- Each constructed affine source has the original coefficient map through its quotient. -/
@[reassoc]
theorem component_base (x : (smoothHilbertSource f).left) :
    OrderedHilbertIdentityQuotientCover.toOriginal f hL x ≫
        invariantLocallyRingedBaseMap e = (test f hL x).hom.toLRSHom := by
  dsimp only [OrderedHilbertIdentityQuotientCover.toOriginal,
    OrderedHilbertIdentityOriginalSection.test]
  rw [Category.assoc]
  exact identityGroundOriginalQuotientMap_globalBase f hL (d x) (E x) (c x) (k x)

/-- The transported original base equals the W240 quotient-defined base on the EXACT source. -/
theorem source_base :
    (sourceTest f hL).hom = OrderedHilbertIdentitySchemeSource.base f hL := by
  apply Sigma.hom_ext
  intro x
  apply Scheme.forgetToLocallyRingedSpace.map_injective
  change (Sigma.ι Q x ≫ (sourceTest f hL).hom).toLRSHom =
    (Sigma.ι Q x ≫ OrderedHilbertIdentitySchemeSource.base f hL).toLRSHom
  rw [Scheme.Hom.comp_toLRSHom, Scheme.Hom.comp_toLRSHom,
    OrderedHilbertIdentitySchemeSource.base_eq,
    OrderedHilbertIdentitySchemeSource.component_toOriginal_assoc, component_base]
  exact congrArg Scheme.Hom.toLRSHom (component f hL x).w

/-- The original Picard source's coefficient square is an equality of locally ringed maps. -/
theorem source_baseSquare :
    OrderedHilbertIdentitySchemeSource.toOriginal f hL ≫ invariantLocallyRingedBaseMap e =
      (sourceTest f hL).hom.toLRSHom := by
  rw [source_base]
  exact (OrderedHilbertIdentitySchemeSource.base_eq f hL).symm

end FLT.Mazur.OrderedHilbertIdentityOriginalBaseSquare

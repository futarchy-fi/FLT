/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertBaseOpenRelation
public import FLT.Mazur.RelativeRelationFppfLocallyRingedDescent

/-!
# Effective scheme quotients of the full relation over actual Hilbert charts

The constructed etale cover and its full original restricted relation give
the actual Hilbert parameter scheme as quotient, with all invariant functions
and the original coefficient base. No global chart coverage is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertBaseOpenChart
open HilbertChart CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsOpenImmersion V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "P₁" => restrictedFst f hL d V c
local notation "P₂" => restrictedSnd f hL d V c
local notation "a" => projection f hL d V c
local notation "H" => restricted_isPullback f hL d V c

/-- The unchanged full restricted original relation is an internal equivalence relation. -/
def restrictedEquivalence : CategoryTheory.EquivalenceRelation P₁ P₂ :=
  IsKernelPair.equivalenceRelation a P₁ P₂ (pullbackIsPullback P₂ P₁) H

/-- The actual Hilbert scheme chart is the full invariant locally ringed quotient. -/
def invariantQuotientIso :
    invariantLocallyRingedSpace (restrictedEquivalence f hL d V c) ≅
      (variableHilbertTest f d V).left.toLocallyRingedSpace :=
  fppfInvariantQuotientIso (restrictedEquivalence f hL d V c) a H

/-- The constructed quotient retains the prescribed geometric projection. -/
@[reassoc]
theorem invariantQuotientIso_projection :
    invariantLocallyRingedProjection (restrictedEquivalence f hL d V c) ≫
      (invariantQuotientIso f hL d V c).hom = (a).left.toLRSHom :=
  fppfInvariantQuotientIso_projection (restrictedEquivalence f hL d V c) a H

/-- The original coefficient map is retained through the full invariant function comparison. -/
theorem invariantQuotientIso_base :
    (invariantQuotientIso f hL d V c).hom ≫
      (variableHilbertTest f d V).hom.toLRSHom =
        invariantLocallyRingedBaseMap (restrictedEquivalence f hL d V c) :=
  fppfInvariantQuotientIso_baseMap (restrictedEquivalence f hL d V c) a H

/-- The geometric chart is the coequalizer of the entire restricted original scheme relation. -/
def schemeCoforkIsColimit : IsColimit (Cofork.ofπ (a).left
    (congrArg Over.Hom.left (H).w)) :=
  isColimitCoforkOfEffectiveEpi (a).left _ ((H).map (Over.forget _)).isLimit

/-- The same full relation coequalizer in locally ringed spaces has the actual scheme model. -/
def locallyRingedQuotientIso : locallyRingedQuotient (p := P₁) (q := P₂) ≅
    (variableHilbertTest f d V).left.toLocallyRingedSpace :=
  fppfLocallyRingedQuotientIso (restrictedEquivalence f hL d V c) a H

end FLT.Mazur.OrderedHilbertBaseOpenChart

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertChangeFppf
public import FLT.Mazur.VariableHilbertSplitChange

/-!
# Effective full parameter quotients for nonsplit fppf translation changes

A translation pulled from an open base has an effective full scheme quotient
along every fppf base cover. No section of that cover is needed. Both independent
translation coordinates remain in the original equal-class relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  [IsOpenImmersion V.hom] [Flat b.left] [LocallyOfFinitePresentation b.left]
  [Surjective b.left] (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "cW" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c
local notation "e" => variableChartEquivalenceRelation f hL d W cW
local notation "g" => baseMarkedChartChange f b d
local notation "H" => variableHilbertChange_isPullback f hL d b c

/-- The full invariant quotient is the actual target scheme for every fppf base cover. -/
def variableHilbertFppfQuotientIso : invariantLocallyRingedSpace e ≅
    (variableHilbertTest f d V).left.toLocallyRingedSpace :=
  fppfInvariantQuotientIso e g H

/-- The full original quotient projection is exactly the geometric parameter change. -/
@[reassoc]
theorem variableHilbertFppfQuotientIso_projection :
    invariantLocallyRingedProjection e ≫ (variableHilbertFppfQuotientIso f hL d b c).hom =
      (g).left.toLRSHom := fppfInvariantQuotientIso_projection e g H

/-- All invariant regular functions retain the original coefficient morphism. -/
theorem variableHilbertFppfQuotientIso_base :
    (variableHilbertFppfQuotientIso f hL d b c).hom ≫
      (variableHilbertTest f d V).hom.toLRSHom = invariantLocallyRingedBaseMap e :=
  fppfInvariantQuotientIso_baseMap e g H

/-- The same scheme is the full locally ringed coequalizer, not only the orbit set. -/
def variableHilbertFppfLocallyRingedIso :
    locallyRingedQuotient (p := variableChartRelationFst f hL d W cW)
      (q := variableChartRelationSnd f hL d W cW) ≅
        (variableHilbertTest f d V).left.toLocallyRingedSpace :=
  fppfLocallyRingedQuotientIso e g H

/-- The target also coequalizes the entire original relation in the category of schemes. -/
def variableHilbertFppfCoforkIsColimit : IsColimit (Cofork.ofπ (g).left
    (congrArg Over.Hom.left (H).w)) :=
  isColimitCoforkOfEffectiveEpi (g).left _ ((H).map (Over.forget _)).isLimit

end FLT.Mazur.HilbertChart

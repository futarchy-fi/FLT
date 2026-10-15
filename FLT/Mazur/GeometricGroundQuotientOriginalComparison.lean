/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertGroundBaseSource
public import FLT.Mazur.VariableHilbertFixedBaseQuotient

/-!
# Constructed geometric ground-quotient maps retain the original quotient

Compose a changed-family quotient chart with the actual original invariant
quotient comparison. Its entire geometric morphism and original coefficient
map are retained. Openness of this composite is not inferred from openness
of the changed-family chart.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] variableChartFixedBaseQuotientMap
  invariantLocallyRingedProjection invariantLocallyRingedBaseMap
variable {R S K : Type} [CommRing R] [CommRing S] [Field K]
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of S) ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) (W : Over (Spec (.of S)))
  (v : (Over.map a).obj W ⟶ V) (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "q" => pullback.snd f a
local instance geometricGroundComparisonSmooth : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "E" => variableChartEquivalenceRelation f hL d V c
local notation "E'" => variableChartEquivalenceRelation q (fixedBaseAmple f a hL) d W
  (fixedBaseTranslationClass f a V W v c)
local notation "u" => groundBaseSourceMap f a hL d V W v k
local notation "l" => groundBaseSourceChart f a hL d V W v k
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W v
/-- The original invariant quotient comparison, with its two quotient objects explicit. -/
@[irreducible]
def geometricGroundQuotientComparison :
    invariantLocallyRingedSpace E' ⟶ invariantLocallyRingedSpace E :=
  variableChartFixedBaseQuotientMap f a hL d V W v c

local notation "J" => geometricGroundQuotientComparison f a hL d V W v c
variable {t : Spec (.of K) ⟶ Spec (.of R)} (b : Over.mk t ⟶ A)
  (z : Spec (.of K) ⟶ (groundBaseSource f a hL d V W v k).left)

/-- The composite is the exact original geometric quotient morphism, including its sheaf map. -/
theorem geometric_ground_quotient_original (hz : z ≫ (u).left = b.left) {Q : Scheme}
    (j : Q.toLocallyRingedSpace ⟶ invariantLocallyRingedSpace E') (w : Spec (.of K) ⟶ Q)
    (hw : w.toLRSHom ≫ j =
      (z ≫ (l).left).toLRSHom ≫ invariantLocallyRingedProjection E') :
    w.toLRSHom ≫ j ≫ J = (b ≫ k).left.toLRSHom ≫ invariantLocallyRingedProjection E := by
  rw [geometricGroundQuotientComparison, ← Category.assoc, hw, Category.assoc,
    variableChartFixedBaseQuotientMap_projection,
    ← Category.assoc, ← Scheme.Hom.comp_toLRSHom]
  have hs : (u).left ≫ k.left = (l).left ≫ (P).left :=
    congrArg Over.Hom.left (groundBaseSource_square f a hL d V W v k)
  rw [Category.assoc z, ← hs, ← Category.assoc z, hz]
  rfl

/-- In particular the composite keeps the original field-to-coefficient map unchanged. -/
theorem geometric_ground_quotient_original_base (hz : z ≫ (u).left = b.left) {Q : Scheme}
    (j : Q.toLocallyRingedSpace ⟶ invariantLocallyRingedSpace E') (w : Spec (.of K) ⟶ Q)
    (hw : w.toLRSHom ≫ j =
      (z ≫ (l).left).toLRSHom ≫ invariantLocallyRingedProjection E') :
    w.toLRSHom ≫ j ≫ J ≫ invariantLocallyRingedBaseMap E = t.toLRSHom := by
  rw [← Category.assoc j J, ← Category.assoc w.toLRSHom,
    geometric_ground_quotient_original f a hL d V W v c k b z hz j w hw,
    Category.assoc, invariantLocallyRingedProjection_baseMap,
    ← Scheme.Hom.comp_toLRSHom, (b ≫ k).w]
  rfl

end FLT.Mazur.HilbertChart.AffineRestriction

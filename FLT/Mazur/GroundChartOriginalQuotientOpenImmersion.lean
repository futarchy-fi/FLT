/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroundChartOriginalQuotientTopology
public import FLT.Mazur.AffineHilbertEtaleRestrictedOpenImmersion

/-!
# The full original ground-chart quotient is a locally ringed open subspace

Effective descent of all original invariant functions upgrades the original
orbit embedding to an open immersion, including the structure sheaf. This
concerns the full original relation on the changed source. It does not assert
scheme effectivity or invariance of the changed-family norm under extra arrows.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open FCurve CartierAbel SchemePicard RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd invariantLocallyRingedProjection
  variableChartFixedBaseQuotientMap restrictedInvariantQuotientMap
variable {R S : Type} [CommRing R] [CommRing S]
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of S) ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) (W : Over (Spec (.of S)))
  (t : (Over.map a).obj W ⟶ V) (c : (relativeFppfSheaf f).obj.obj (op V))
local instance groundOriginalOpenSmooth : SmoothOfRelativeDimension 1 (pullback.snd f a) :=
  MorphismProperty.pullback_snd _ _ inferInstance
variable {B : Over (Spec (.of S))}
  (l : B ⟶ variableHilbertTest (pullback.snd f a) d W)
local notation "k" => groundOriginalChart f a hL d V W t l
local notation "D" => equivalence f hL d V c k
local notation "E" => variableChartEquivalenceRelation f hL d V c
local notation "j" => restrictedInvariantQuotientMap f hL d V c k

/-- Full original descent upgrades the ground-chart orbit embedding to an LRS open immersion. -/
theorem groundOriginalQuotient_isOpenImmersion
    [Etale V.hom] [Etale t.left] [IsOpenImmersion l.left] :
    LocallyRingedSpace.IsOpenImmersion (j) :=
  etaleRestrictedInvariantQuotientMap_isOpenImmersion f hL d V c k

/-- The open comparison retains the original coefficient map on its entire structure sheaf. -/
theorem groundOriginalQuotient_base :
    j ≫ invariantLocallyRingedBaseMap E = invariantLocallyRingedBaseMap D := by
  apply invariantMap_hom_ext D
  rw [restrictedInvariantQuotientMap_projection_assoc,
    invariantLocallyRingedProjection_baseMap, invariantLocallyRingedProjection_baseMap,
    ← Scheme.Hom.comp_toLRSHom, (k).w]

/-- Any effective scheme chart of the full quotient is an original scheme chart. -/
theorem groundOriginal_schemeChart [Etale V.hom] [Etale t.left] [IsOpenImmersion l.left]
    {Q : Scheme} (i : Q.toLocallyRingedSpace ⟶ invariantLocallyRingedSpace D)
    [LocallyRingedSpace.IsOpenImmersion i] :
    LocallyRingedSpace.IsOpenImmersion (i ≫ j) := by
  let _ := groundOriginalQuotient_isOpenImmersion f a hL d V W t c l
  infer_instance

/-- The chart transfer preserves whole test morphisms, including nonreduced tests. -/
theorem groundOriginal_schemeChart_test {T Q : Scheme}
    (i : Q.toLocallyRingedSpace ⟶ invariantLocallyRingedSpace D)
    (z : T ⟶ Q) (b : T ⟶ B.left)
    (hz : z.toLRSHom ≫ i = b.toLRSHom ≫ invariantLocallyRingedProjection D) :
    z.toLRSHom ≫ i ≫ j = (b ≫ (k).left).toLRSHom ≫
      invariantLocallyRingedProjection E := by
  rw [← Category.assoc, hz, Category.assoc, restrictedInvariantQuotientMap_projection,
    ← Scheme.Hom.comp_toLRSHom_assoc]

end FLT.Mazur.HilbertChart.AffineRestriction

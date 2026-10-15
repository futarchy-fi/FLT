/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertFixedBaseQuotient
public import FLT.Mazur.VariableHilbertGroundBaseCartesian
public import FLT.Mazur.VariableHilbertEtaleRelation
public import FLT.Mazur.RelativeRelationInvariantMapOpen

/-!
# Topological openness of the original ground-quotient comparison

Etale refinement of translation parameters gives an open map from the changed
invariant quotient to the original one. Every open changed-family chart has
open image, saturated by all original arrows. Injectivity and identification
of the invariant structure sheaves are separate descent questions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open FCurve CartierAbel SchemePicard RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S : Type} [CommRing R] [CommRing S]
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ S]
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of S) ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) (W : Over (Spec (.of S)))
  (t : (Over.map a).obj W ⟶ V) (c : (relativeFppfSheaf f).obj.obj (op V))
  [Etale V.hom] [Etale t.left]
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W t
local notation "J" => variableChartFixedBaseQuotientMap f a hL d V W t c

/-- The actual ground-quotient comparison is open on underlying topological spaces. -/
theorem variableChartFixedBaseQuotientMap_isOpenMap : IsOpenMap (J).base := by
  let _ : Etale (P).left := variableHilbertGroundBase_property f a hL d V W t
    (@Etale) inferInstance
  exact invariantMap_isOpenMap _ _ _ _ _ _ (P).left.isOpenMap
    (variableChartRelationSnd f hL d V c).left.isOpenMap

/-- Any open chart of the changed quotient has an open image in the original quotient. -/
theorem variableChartFixedBaseQuotientMap_chart_isOpenMap {Q : Scheme}
    (j : Q.toLocallyRingedSpace ⟶ _)
    [hj : LocallyRingedSpace.IsOpenImmersion j] : IsOpenMap (j ≫ J).base := by
  rw [LocallyRingedSpace.comp_base]
  exact (variableChartFixedBaseQuotientMap_isOpenMap f a hL d V W t c).comp
    hj.base_open.isOpenMap

end FLT.Mazur.HilbertChart

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonCompletion
public import FLT.Mazur.PolygonSplitNodeCompletion
public import FLT.Mazur.CurveNodeOpenCover
public import FLT.Mazur.PolygonPinchingFlatBaseChange
public import FLT.Mazur.PolygonConnected
public import FLT.Mazur.PolygonPureDimension

/-!
# Nodal fiber core of the specified polygon

The split-node and one-gon completion models descend through the actual
open charts. Connectedness, reducedness and pure dimension then assemble
the nodal fiber core for every supplied positive polygon cocone.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.PolygonNodalCore
open PolygonPinching FCurve.CurveNode
variable (K : Type u) [Field K]

theorem cyclic (n : ℕ) (hn : 2 ≤ n) :
    let :=  cyclic_lfp K n hn
    AtWorstNodes (PolygonCyclicAtlas.toBase K n hn) := by
  let :=  cyclic_lfp K n hn
  apply CurveNodeOpenCover.of_openCover _ (PolygonCyclicNormalizationFinite.targetCover K n hn)
  intro i
  change AtWorstNodes (PolygonCyclicAtlas.chart K n hn i ≫ PolygonCyclicAtlas.toBase K n hn)
  simpa only [PolygonCyclicAtlas.chart_toBase] using PolygonSplitNodeCompletion.atWorstNodes K

theorem oneGon : letI := oneGon_lfp K
    AtWorstNodes (OneGonGluing.toBase K) := by
  let :=  oneGon_lfp K
  apply CurveNodeOpenCover.of_openCover _ (OneGonNormalizationFinite.targetCover K)
  intro i
  cases i
  · change AtWorstNodes (OneGonGluing.node K ≫ OneGonGluing.toBase K)
    simpa only [OneGonGluing.node_toBase] using PolygonOneGonCompletion.atWorstNodes K
  · change AtWorstNodes (OneGonGluing.torus K ≫ OneGonGluing.toBase K)
    have : Smooth (OneGonGluing.torusToBase K) := by
      change Smooth (MultiplicativeGroupScheme.gm K).hom
      infer_instance
    have ht : AtWorstNodes (OneGonGluing.torusToBase K) := by
      change AtWorstNodes (MultiplicativeGroupScheme.gm K).hom
      exact atWorstNodes_of_smooth _
    simpa only [OneGonGluing.torus_toBase] using ht

theorem atlas (n : ℕ) [NeZero n] : AtWorstNodes (PolygonAtlas.polygon K n).hom := by
  rcases n with _ | (_ | n)
  · exact (NeZero.ne 0 rfl).elim
  · exact oneGon K
  · exact cyclic K (n + 2) (by omega)

variable (n : ℕ) [NeZero n] (hn : 0 < n) {C : Over (Spec (.of K))}
  (p : components K n ⟶ C) (q : PolygonPinching.nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
include h in
/-- The actual pinched polygon has only smooth points and split nodes. -/
theorem nodes : letI := polygon_lfp K n hn p q h
    AtWorstNodes C.hom := by
  let :=  polygon_lfp K n hn p q h
  let e := (Over.forget (Spec (.of K))).mapIso (polygonIso K n hn p q h)
  apply CurveNodeOpenCover.of_surjective C.hom e.hom e.hom.homeomorph.surjective
  simpa only [e, Functor.mapIso_hom, Over.forget_map, Over.w] using atlas K n

include h in
/-- Every specified positive polygon over a field satisfies the nodal fiber core. -/
theorem nodalFiberCore : FCurve.CurveFiberHypotheses.NodalFiberCore C.hom := by
  let hc := PolygonConnected.connected K n hn p q h
  let e := (Over.forget (Spec (.of K))).mapIso (polygonIso K n hn p q h)
  have hred : IsReduced ((Over.forget (Spec (.of K))).obj (PolygonAtlas.polygon K n)) :=
    inferInstanceAs (IsReduced (PolygonAtlas.polygon K n).left)
  have hr : IsReduced C.left := isReduced_of_isOpenImmersion e.inv
  exact ⟨polygon_lfp K n hn p q h, inferInstance, hc, hr,
    PolygonPureDimension.pureDimension K n hn p q h, nodes K n hn p q h⟩
end FLT.Mazur.PolygonNodalCore

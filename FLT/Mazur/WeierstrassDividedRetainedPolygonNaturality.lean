/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingBranchSwapNaturality
public import FLT.Mazur.PolygonInfinitesimalChartRestriction
public import FLT.Mazur.WeierstrassDividedRetainedPolygonMaps

/-!
# Retained comparison maps preserve the original arithmetic base

The full oriented maps commute with explicit coefficient substitution, so
both arms can be compared at every quotient order without altering their labels.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing
universe u
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (t : R) (s : S) [Fact (IsNilpotent t)] [Fact (IsNilpotent s)]
  (hs : f t = s) (k : ℕ)

/-- Both full retained maps commute with the specified polygon coefficient projection. -/
@[reassoc] theorem retainedPolygonMap_parameterProjection (a : Fin k) (b : Bool) :
    retainedPolygonMap S s k a b ≫
      PolygonInfinitesimal.parameterProjection f t s hs (2 * k + 3) (by omega) =
    Spec.map (CommRingCat.ofHom (ringMap f t s hs)) ≫ retainedPolygonMap R t k a b := by
  cases b
  · simp only [retainedPolygonMap_false]
    exact PolygonInfinitesimal.chart_parameterProjection f t s hs _ _ _
  · simp only [retainedPolygonMap, ↓reduceIte, Category.assoc]
    rw [PolygonInfinitesimal.chart_parameterProjection, branchSwapIso_ringMap_assoc]

omit [Fact (IsNilpotent t)] in
/-- Reversing the full node preserves its original structure morphism. -/
@[reassoc] theorem retainedPolygonSwap_base :
    (branchSwapIso R t).hom ≫ chartStructure R t = chartStructure R t := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (branchSwapMap t).commutes r

/-- The retained comparison is over the unchanged coefficient spectrum. -/
@[reassoc] theorem retainedPolygonMap_base (a : Fin k) (b : Bool) :
    retainedPolygonMap R t k a b ≫
      PolygonInfinitesimal.toBase R t (2 * k + 3) (by omega) = chartStructure R t := by
  cases b
  · rw [retainedPolygonMap_false, PolygonInfinitesimal.chart_toBase]
  · simp only [retainedPolygonMap, ↓reduceIte, Category.assoc,
      PolygonInfinitesimal.chart_toBase, retainedPolygonSwap_base]

end FLT.Mazur.WeierstrassDividedDepth

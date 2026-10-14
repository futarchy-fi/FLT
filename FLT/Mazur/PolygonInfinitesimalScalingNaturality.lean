/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalScaling
public import FLT.Mazur.PolygonInfinitesimalChartRestriction
public import FLT.Mazur.PolygonSmoothingScalingNaturality

/-!
# Whole infinitesimal scaling under original coefficient restrictions

The full glued automorphisms commute with arbitrary coefficient projections.
In particular the actual adjacent original stages retain their full scaling
maps, including every original node and every nonreduced neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.PolygonInfinitesimal
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (t : R) (s : S) [Fact (IsNilpotent t)] [Fact (IsNilpotent s)]
  (hs : f t = s) (n : ℕ) (h : 2 ≤ n)

/-- Coefficient projection intertwines the actual full-polygon scaling automorphisms. -/
@[reassoc] theorem scaling_parameterProjection (a : Rˣ) :
    scaling S s n h (Units.map f a) ≫ parameterProjection f t s hs n h =
      parameterProjection f t s hs n h ≫ scaling R t n h a := by
  apply chart_hom_ext S s n h
  intro i
  rw [chart_scaling_assoc, chart_parameterProjection, chart_parameterProjection_assoc,
    chart_scaling, ← Category.assoc, ← Category.assoc]
  congr 1
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext (ringMap_reciprocalScale f t s hs a).symm

end FLT.Mazur.PolygonInfinitesimal

namespace FLT.Mazur.PolygonInfinitesimalStages
variable (R : Type u) [CommRing R] (m n : ℕ) (h : 2 ≤ n)

/-- The actual adjacent original stage restrictions retain the constructed whole-stage scaling. -/
@[reassoc] theorem scaling_stageRestriction (a : (Ring R (m + 1))ˣ) :
    PolygonInfinitesimal.scaling (Ring R m) (parameter R m) n h
        (Units.map (restriction R m).toRingHom a) ≫ stageRestriction R m n h =
      stageRestriction R m n h ≫
        PolygonInfinitesimal.scaling (Ring R (m + 1)) (parameter R (m + 1)) n h a :=
  PolygonInfinitesimal.scaling_parameterProjection (restriction R m).toRingHom
    (parameter R (m + 1)) (parameter R m) (restriction_parameter R m) n h a

end FLT.Mazur.PolygonInfinitesimalStages

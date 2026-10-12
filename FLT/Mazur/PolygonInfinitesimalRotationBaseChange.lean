/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalCoefficientTransport
public import FLT.Mazur.PolygonInfinitesimalRotation

/-!
# Coefficient naturality of infinitesimal rotations

The constructed rotation commutes with the actual coefficient projection,
including projections to an explicitly chosen target parameter. Thus the
cyclic symmetry is retained by every nilpotent coefficient base change.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (t : R) [Fact (IsNilpotent t)] [Fact (IsNilpotent (algebraMap R S t))]
  (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Cyclic rotation commutes with the assembled coefficient projection on every chart. -/
@[reassoc] theorem rotation_coefficientProjection (a : ZMod n) :
    rotation S (algebraMap R S t) n h a ≫ coefficientProjection R S t n h =
      coefficientProjection R S t n h ≫ rotation R t n h a := by
  apply chart_hom_ext S (algebraMap R S t) n h
  intro i
  rw [chart_rotation_assoc, chart_coefficientProjection,
    chart_coefficientProjection_assoc, chart_rotation]

end FLT.Mazur.PolygonInfinitesimal

namespace FLT.Mazur.PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (t : R) (s : S) [Fact (IsNilpotent t)] [Fact (IsNilpotent s)]
  (hs : f t = s) (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Rotation retains a specified coefficient map and its actual target parameter. -/
@[reassoc] theorem rotation_parameterProjection (a : ZMod n) :
    rotation S s n h a ≫ parameterProjection f t s hs n h =
      parameterProjection f t s hs n h ≫ rotation R t n h a := by
  subst s
  let _ := f.toAlgebra
  exact rotation_coefficientProjection R S t n h a

end FLT.Mazur.PolygonInfinitesimal

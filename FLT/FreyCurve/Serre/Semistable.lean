/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Basic
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Semistability of the integral Frey model

The discriminant and `c₄` never vanish simultaneously in a residue field.
This gives good or multiplicative reduction over discrete valuation rings.
-/

@[expose] public section

open FreyPackage WeierstrassCurve

/-- The integral Frey model has the usual polynomial formula for its `c₄` invariant. -/
theorem FreyCurve.c₄_int (P : FreyPackage) :
    P.freyCurveInt.c₄ = (P.a ^ P.p) ^ 2 + P.a ^ P.p * P.b ^ P.p + (P.b ^ P.p) ^ 2 := by
  have h := congrArg WeierstrassCurve.c₄ (FreyCurve.map P)
  simp only [map_c₄, eq_intCast] at h
  exact_mod_cast h.trans (FreyCurve.c₄ P)

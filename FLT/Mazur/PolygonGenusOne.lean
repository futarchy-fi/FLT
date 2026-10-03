/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCohomologyIncidence
public import FLT.Mazur.PolygonConstantSections
public import FLT.Mazur.PolygonProper
public import FLT.Mazur.PolygonDimension
public import FLT.Mazur.ProperCurveGenus
/-!
# Genus one of the polygon

Properness, dimension one, and canonical constant sections supply the
curve hypotheses. The actual H1 incidence calculation gives genus one.
The existing proper-cohomology genus API uses fields in `Type`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
namespace FLT.Mazur.PolygonGenusOne
open PolygonPinching FCurve
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
include h in
/-- Every specified positive-size polygon pinching cocone has genus one. -/
theorem genus_one :
    let := PolygonProper.proper K n hn p q h
    curveGenus C.hom (PolygonDimension.dimension K n hn p q h)
      (PolygonConstantSections.constants K n hn p q h) = 1 := by
  let := PolygonProper.proper K n hn p q h
  exact PolygonCohomologyIncidence.h1_finrank K n hn p q h
end FLT.Mazur.PolygonGenusOne

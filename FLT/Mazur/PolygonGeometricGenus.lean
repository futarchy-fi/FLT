/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFieldExtension
public import FLT.Mazur.PolygonNodalCore
public import FLT.Mazur.PolygonGenusOne
public import FLT.Mazur.NodalGeometricFiberGenus

/-!
# Geometric genus-one nodal fibers of polygons

Field-extension comparison supplies the specified cocone on every geometric
pullback. The nodal core and the actual H1 computation give its genus-one core.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonGeometricGenus
open PolygonPinching FCurve.CurveFiberHypotheses
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
include h in
/-- The specified polygon has the full necessary genus-one nodal fiber core. -/
theorem fiberCore [IsProper C.hom] : NodalGenusOneFiberCore C.hom := by
  refine ⟨PolygonNodalCore.nodalFiberCore K n hn p q h,
    PolygonConstantSections.constants K n hn p q h, ?_⟩
  exact PolygonGenusOne.genus_one K n hn p q h

include h in
/-- Every geometric fiber of the specified polygon satisfies the nodal genus-one contract. -/
theorem geometricFibers : let := PolygonProper.proper K n hn p q h
    NodalGenusOneGeometricFibers C.hom := by
  let := PolygonProper.proper K n hn p q h
  refine ⟨fun L _ _ g Y fst snd hs ↦ ?_⟩
  let : IsProper snd := MorphismProperty.of_isPullback hs (inferInstance : IsProper C.hom)
  obtain ⟨p', q', hh⟩ :=
    PolygonFieldExtension.exists_cocone_of_isPullback K L n hn p q h g fst snd hs
  let : IsProper (Over.mk snd).hom := inferInstanceAs (IsProper snd)
  exact fiberCore L n hn p' q' hh
end FLT.Mazur.PolygonGeometricGenus

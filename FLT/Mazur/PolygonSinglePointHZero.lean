/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSinglePointLoopKernel

/-!
# Actual H0 of every original single-point polygon power

Normalization and canonical endpoint gluing identify the whole polygon H0
with the equal-endpoint kernel on its marked projective line. In positive
degree its dimension is the pole bound, including dimension one for O(P).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonSinglePointHZero

open FCurve PolygonPinching PolygonSinglePointLineNormalization
open PolygonNormalizationLinearSections PolygonSinglePointHZeroCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] PolygonComponentHZeroMatching.h0Equiv ownEquiv componentEquiv

variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Kˣ) (j : Fin n) (m : ℕ)

/-- The whole original polygon H0 is linearly the marked equal-endpoint kernel. -/
def equiv : ModuleScalarH C.hom (pointPower K n hn p q h a j m) 0 ≃ₗ[K]
    LinearMap.ker (ProjectiveLinePointLoopMatching.difference K a m) := by
  let hI := (PolygonMarkedSections.section_cartier K n p hn q h a j).1.pow m
  exact (PolygonComponentHZeroMatching.h0Equiv K n hn p q h (pointPower K n hn p q h a j m)
    hI.divisorLineBundle_locallyFreeRankOne).trans
    (PolygonSinglePointLoopKernel.equiv K n hn p q h a j m)

/-- Its value is restriction of the original class to its original marked component. -/
theorem equiv_val (x : ModuleScalarH C.hom (pointPower K n hn p q h a j m) 0) :
    (equiv K n hn p q h a j m x).val =
      ownEquiv K n hn p q h a j m
        (componentEquiv K n p (pointPower K n hn p q h a j m)
          (moduleScalarHMap C.hom ((Scheme.Modules.pullbackPushforwardAdjunction p.left).unit.app
            (pointPower K n hn p q h a j m)) 0 x) j) := by
  change (PolygonSinglePointLoopKernel.equiv K n hn p q h a j m _).val = _
  rw [PolygonSinglePointLoopKernel.equiv_val,
    PolygonSinglePointMatchingCoordinates.familyCoordinates_fst]
  exact congrArg (fun v : PolygonSinglePointScalarMatching.Family K n hn p q h a j m ↦
    ownEquiv K n hn p q h a j m (v j))
    (PolygonComponentHZeroMatching.h0Equiv_val K n hn p q h
      (pointPower K n hn p q h a j m)
      (EffectiveCartier.divisorLineBundle_locallyFreeRankOne
        ((PolygonMarkedSections.section_cartier K n p hn q h a j).1.pow m)) x)

/-- Every positive original single-point power has exactly its pole-bound dimension. -/
theorem finrank (hm : 0 < m) :
    Module.finrank K (ModuleScalarH C.hom (pointPower K n hn p q h a j m) 0) = m :=
  (equiv K n hn p q h a j m).finrank_eq.trans
    (ProjectiveLinePointLoopMatching.finrank_kernel K a m hm)

/-- The original single-point line has exactly one global-section dimension. -/
theorem finrank_one :
    Module.finrank K (ModuleScalarH C.hom (pointPower K n hn p q h a j 1) 0) = 1 :=
  finrank K n hn p q h a j 1 (by decide)

end FLT.Mazur.PolygonSinglePointHZero

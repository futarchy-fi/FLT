/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCanonicalCyclicity
public import FLT.Mazur.ToricFiniteSubgroupComparison
public import FLT.Mazur.ArithmeticOneGonArbitrarySubgroupPullback

/-!
# Prescribed original subgroups on the genuine adic boundary

Every original one-gon subgroup of rank n is the actual field pullback of
the constructed complete-base subgroup. The comparison retains the prescribed
full-curve isomorphism and the entire subgroup ideal, including nonetale fibers.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
open CharacterSchemeBaseChange ArithmeticOneGonGeneralizedCurve

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]
  (K : Type) [Field K] [Algebra R K] (hzero : algebraMap R K t = 0)

variable (H : (PolygonGeneralizedCurve.curve K 1 Nat.zero_lt_one
  (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
  (OneGonGlobalPushout.isPushout K Nat.zero_lt_one)).FiniteSubgroup n)

/-- The prescribed original subgroup is the actual boundary fiber of the canonical subgroup. -/
def prescribedBoundaryIso : CompatibleIso H
    ((canonicalFiniteSubgroup I t ht n).baseChange (baseMap R K)) :=
  H.toricCompatibleIsoOver _
    (ArithmeticOneGonBoundaryFiber.curveIso K t (complementaryFactor_isUnit I t ht) hzero)
    (ArithmeticOneGonFiberTorus.torusIso K t hzero)

/-- This comparison retains the existing full arithmetic pinching isomorphism. -/
theorem prescribedBoundaryIso_curve : (prescribedBoundaryIso I t ht n K hzero H).curve =
    ArithmeticOneGonBoundaryFiber.curveIso K t (complementaryFactor_isUnit I t ht) hzero :=
  H.toricCompatibleIsoOver_curve _ _ _

attribute [local irreducible] prescribedBoundaryIso

/-- Every multiplicity of the prescribed ideal occurs in the actual complete-base pullback. -/
theorem prescribedBoundary_ideal :
    ((canonicalFiniteSubgroup I t ht n).baseChange (baseMap R K)).ideal =
      H.ideal.comap (ArithmeticOneGonBoundaryFiber.curveIso K t
        (complementaryFactor_isUnit I t ht) hzero).inv.curve.left := by
  let e := prescribedBoundaryIso I t ht n K hzero H
  have h := ideal_transport _ _ e.curve e.subgroup e.compatible
  rw [show e.curve = _ from prescribedBoundaryIso_curve I t ht n K hzero H] at h
  exact h

/-- The original whole-curve defining ideal is retained by the actual base-change projection. -/
theorem canonicalIdeal_boundary_comap :
    (canonicalFiniteSubgroup I t ht n).ideal.comap
        (CategoryTheory.Limits.pullback.fst
          (curve t (complementaryFactor_isUnit I t ht)).curve.hom (baseMap R K)) =
      H.ideal.comap (ArithmeticOneGonBoundaryFiber.curveIso K t
        (complementaryFactor_isUnit I t ht) hzero).inv.curve.left := by
  rw [← baseChange_ideal]
  exact prescribedBoundary_ideal I t ht n K hzero H

end FLT.Mazur.OneGonAdicCharacterTower

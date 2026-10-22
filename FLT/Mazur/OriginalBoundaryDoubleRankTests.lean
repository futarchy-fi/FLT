/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryRankCollision
public import FLT.Mazur.RelativeDoubleRankTestDetection

/-!
# Full independent rank tests on the original boundary scalar kernel pair

The original ring, boundary scheme and both scalar endpoints stay fixed.
All points, including the rank collisions, lift at every pair of orders.
Both source pullbacks are finite on each stage, and the entire family detects
sections on locally Noetherian tests without a Noetherian scalar-ring assumption.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (J : A.IdealSheafData)
local instance boundaryDoubleOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance boundaryDoubleOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance boundaryDoubleOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι

/-- Every original boundary scalar pair lifts at every two orders, with no matching-rank input. -/
theorem originalBoundary_doubleRank_coverage (r s : ℕ) (z : (pullback f f : Scheme)) :
    ∃ (n m : ℕ) (w : doubleRankThickening (Over.mk p) x y n m r s),
      doubleRankMap (Over.mk p) x y n m r s w = z :=
  exists_doubleRank_lift (Over.mk p) x y r s z

omit [QuasiCompact p] in
/-- The exact original scalar equation survives on the whole two-rank thickening. -/
theorem originalBoundary_doubleRank_scalar_square (n m r s : ℕ) :
    doubleRankMap (Over.mk p) x y n m r s ≫ pullback.fst f f ≫ f =
      doubleRankMap (Over.mk p) x y n m r s ≫ pullback.snd f f ≫ f := by
  rw [pullback.condition]

omit [QuasiCompact p] in
/-- Actual unequal-rank boundary pairs are covered too, rather than silently discarded. -/
theorem originalBoundary_rankCollision_iff_doubleRank (r s : ℕ)
    (z : (pullback f f : Scheme)) :
    z ∈ rankCollision (Over.mk p) x y ↔
      ∃ (n m : ℕ), n ≠ m ∧ ∃ w : doubleRankThickening (Over.mk p) x y n m r s,
        doubleRankMap (Over.mk p) x y n m r s w = z := by
  constructor
  · rintro ⟨n, m, hnm, hn, hm⟩
    have hz : z ∈ Set.range (doubleRankMap (Over.mk p) x y n m r s) := by
      rw [doubleRankMap_range]
      exact ⟨hn, hm⟩
    exact ⟨n, m, hnm, hz⟩
  · rintro ⟨n, m, hnm, w, rfl⟩
    exact ⟨n, m, hnm, doubleRankMap_endpoints (Over.mk p) x y n m r s w⟩

/-- The original geometric rank bound gives a finite rectangle of boundary rank indices. -/
theorem originalBoundary_doubleRank_bounded [TopologicalSpace.NoetherianSpace A] (r s : ℕ) :
    ∃ N : ℕ, ∀ z : (pullback f f : Scheme), ∃ (n m : ℕ), n ≤ N ∧ m ≤ N ∧
      ∃ w : doubleRankThickening (Over.mk p) x y n m r s,
        doubleRankMap (Over.mk p) x y n m r s w = z :=
  exists_bounded_doubleRank_lifts (Over.mk p) x y r s

/-- Finiteness concerns both full original sources, not just their residue-field fibers. -/
theorem originalBoundary_doubleRank_sources_finite [LocallyQuasiFinite p] (n m r s : ℕ) :
    IsFinite (pullback.snd p (doubleRankMap (Over.mk p) x y n m r s ≫ x)) ∧
      IsFinite (pullback.snd p (doubleRankMap (Over.mk p) x y n m r s ≫ y)) := by
  let _ : LocallyQuasiFinite (Over.mk p).hom := ‹LocallyQuasiFinite p›
  exact doubleRank_both_sources_finite (Over.mk p) x y n m r s

variable [IsNoetherian A]

/-- Every locally Noetherian test detects full boundary coefficients from the independent stages. -/
theorem originalBoundary_test_eq_of_doubleRank {T : Scheme.{0}} [IsLocallyNoetherian T]
    (v : T ⟶ pullback f f) (a b : Γ(pullback f f, ⊤))
    (h : ∀ n m r s : ℕ, (doubleRankMap (Over.mk p) x y n m r s).appTop a =
      (doubleRankMap (Over.mk p) x y n m r s).appTop b) : v.appTop a = v.appTop b :=
  test_eq_of_doubleRank_stages (Over.mk p) x y v a b h

end FLT.Mazur.EquivalenceRelationOrderedFrames

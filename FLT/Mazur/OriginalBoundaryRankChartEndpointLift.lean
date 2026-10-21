/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryNilpotentEndpointLift
public import FLT.Mazur.OriginalBoundaryRankStageDenseCoverage

/-!
# Constructed original endpoint lifts on all affine rank-stage charts

Full endpoint finiteness comes from exact original rank, and Noetherianity
comes from the geometric base and coefficient scheme. Dense stage coverage
restricts to every affine open chart. The resulting boundary arrows preserve
the first endpoint on the entire nonreduced chart; no finite branch is chosen.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B U : Scheme.{0}} {p q : D ⟶ A} [IsAffine A]
  [Etale p] [IsSeparated p] [QuasiCompact p] [LocallyQuasiFinite p]
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
local instance rankChartOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance rankChartOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance rankChartOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local instance rankChartOver_quasiFinite : LocallyQuasiFinite (Over.mk p).hom :=
  ‹LocallyQuasiFinite p›
local instance rankChartBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
local notation "x" => pullback.fst f f ≫ J.subschemeι
attribute [local irreducible] scalarMorphism

omit [IsAffine A] in
/-- Every map to a full rank stage has a finite whole endpoint pullback, not just open charts. -/
theorem originalBoundary_rankChart_endpoint_finite
    (t : B ⟶ pullback f f) (n k : ℕ)
    (u : U ⟶ rankPullbackThickening (Over.mk p) (t ≫ x) n k) :
    IsFinite (pullback.snd p
      ((u ≫ rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t) ≫ x)) := by
  apply finite_pullback_of_exactRank (Over.mk p) n
  rintro _ ⟨v, rfl⟩
  exact rankPullback_endpoint (Over.mk p) (t ≫ x) n k (u v)

variable [IsLocallyNoetherian A] [IsLocallyNoetherian B] [IsAffine U]

/-- Geometric Noetherianity supplies actual nonreduced original arrows on every affine chart. -/
theorem originalBoundary_rankChart_endpoint_lift
    (e : CategoryTheory.EquivalenceRelation p q) (t : B ⟶ pullback f f) (n k : ℕ)
    (u : U ⟶ rankPullbackThickening (Over.mk p) (t ≫ x) n k) [IsOpenImmersion u]
    (h : Dense ((rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t) ⁻¹' Set.range c)) :
    ∃ d : U ⟶ pullback p J.subschemeι,
      d ≫ pullback.snd p J.subschemeι =
        (u ≫ rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t) ≫ pullback.fst f f ∧
      pullback.snd c (u ≫ rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t) ≫ d =
        pullback.fst c (u ≫ rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t) := by
  let _ : IsLocallyNoetherian (rankPullbackThickening (Over.mk p) (t ≫ x) n k) :=
    LocallyOfFiniteType.isLocallyNoetherian (rankPullbackMap (Over.mk p) (t ≫ x) n k)
  let _ : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion u
  let _ : IsNoetherian U := ⟨⟩
  let _ := originalBoundary_rankChart_endpoint_finite J t n k u
  apply originalBoundary_nilpotent_boundary_lift e J hJ
    (u ≫ rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t)
  exact h.preimage u.isOpenMap

end FLT.Mazur.EquivalenceRelationOrderedFrames

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryFieldArrowRank
public import FLT.Mazur.RankStageOriginalTestEquations

/-!
# Constructed finite-stage tests for original field arrows

Every equal-rank pair has actual common boundary factors at all orders.
Existence of an original field arrow is equivalent, without rank assumptions,
to one full endpoint-equation witness on a constructed finite stage.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance fieldEquationOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance fieldEquationOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance fieldEquationOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (J : A.IdealSheafData) {K : Type} [Field K]

open RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f₀" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "I" n:max a:max ha:max k:max => rankStageCoreBoundaryIdeal e n a ha J k
local notation "g" n:max a:max ha:max k:max => rankStageCoreOriginalBoundaryMap e n a ha J k
variable (hJ : J.comap p = J.comap q)
attribute [local irreducible] rankStageCore rankStageCoreBoundaryIdeal
  rankStageCoreOriginalBoundaryMap rankStageBoundaryOriginalScalars

/-- Same-rank original field tests have constructed exact finite-stage tests at every order. -/
theorem originalBoundary_field_test_common_stage (n : ℕ)
    (t : Spec (.of K) ⟶ pullback f₀ f₀)
    (hx : (t ≫ pullback.fst f₀ f₀ ≫ J.subschemeι) (IsLocalRing.closedPoint K) ∈
      exactRank (Over.mk p) n)
    (hy : (t ≫ pullback.snd f₀ f₀ ≫ J.subschemeι) (IsLocalRing.closedPoint K) ∈
      exactRank (Over.mk p) n) :
    ∃ (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n),
      ∀ k, ∃ x y : Spec (.of K) ⟶ (I n a ha k).subscheme,
        ∃ hx' : x ≫ g n a ha k = t ≫ pullback.fst f₀ f₀,
        ∃ hy' : y ≫ g n a ha k = t ≫ pullback.snd f₀ f₀,
          rankStageOriginalTestEquations e n a ha J hJ k t x y hx' hy' ↔
            ∃ d : Spec (.of K) ⟶ pullback p J.subschemeι,
              d ≫ pullback.snd p J.subschemeι = t ≫ pullback.fst f₀ f₀ ∧
              d ≫ InvariantIdealRelation.snd J p q hJ = t ≫ pullback.snd f₀ f₀ := by
  obtain ⟨a, ha, hc⟩ := exists_rankStage_field_boundary_pair e J n
    (t ≫ pullback.fst f₀ f₀) (t ≫ pullback.snd f₀ f₀) hx hy
  refine ⟨a, ha, fun k ↦ ?_⟩
  obtain ⟨x, y, hx', hy'⟩ := hc k
  exact ⟨x, y, hx', hy', rankStageOriginalTestEquations_iff e n a ha J hJ k t x y hx' hy'⟩

/-- Original field arrows are exactly finite-stage equation witnesses, with no supplied factors. -/
theorem originalBoundary_field_arrow_iff_exists_stage_equations
    (t : Spec (.of K) ⟶ pullback f₀ f₀) :
    (∃ d : Spec (.of K) ⟶ pullback p J.subschemeι,
      d ≫ pullback.snd p J.subschemeι = t ≫ pullback.fst f₀ f₀ ∧
      d ≫ InvariantIdealRelation.snd J p q hJ = t ≫ pullback.snd f₀ f₀) ↔
    ∃ (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
      (k : ℕ) (x y : Spec (.of K) ⟶ (I n a ha k).subscheme)
      (hx : x ≫ g n a ha k = t ≫ pullback.fst f₀ f₀)
      (hy : y ≫ g n a ha k = t ≫ pullback.snd f₀ f₀),
      rankStageOriginalTestEquations e n a ha J hJ k t x y hx hy := by
  constructor
  · rintro ⟨d, hd, hd'⟩
    obtain ⟨n, a, ha, hc⟩ := originalBoundary_field_arrow_common_core e J hJ
      (t ≫ pullback.fst f₀ f₀) (t ≫ pullback.snd f₀ f₀) d hd hd'
    obtain ⟨x, y, hx, hy⟩ := hc 0
    exact ⟨n, a, ha, 0, x, y, hx, hy,
      (rankStageOriginalTestEquations_iff e n a ha J hJ 0 t x y hx hy).mpr ⟨d, hd, hd'⟩⟩
  · rintro ⟨n, a, ha, k, x, y, hx, hy, ht⟩
    exact (rankStageOriginalTestEquations_iff e n a ha J hJ k t x y hx hy).mp ht

end FLT.Mazur.EquivalenceRelationOrderedFrames

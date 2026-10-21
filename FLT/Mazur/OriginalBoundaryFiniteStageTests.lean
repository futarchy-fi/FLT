/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageBoundaryRelationPullback

/-!
# Full original tests detected by a finite-stage endpoint quotient

For an original scalar-kernel test with both endpoints in one actual rank-core
boundary, relation lifting is exactly vanishing of the full stage endpoint ideal.
The scalar equation is constructed from the prescribed original endpoints.
This applies to residue-field tests and to nonreduced scheme tests alike.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeScalarImageQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rankStageCore rankStageCoreBoundaryIdeal
  rankStageCoreOriginalBoundaryMap originalBoundaryKernelImage
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance stageResidueOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance stageResidueOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance stageResidueOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q) (k : ℕ)
set_option quotPrecheck false
local notation "C" => rankStageCore e n a ha k
local notation "r" => (rankStageFirst (p := p) n k).resLE C _ le_rfl
local notation "s" => (rankStageSecond e n k).resLE C _
  (rankStageCore_invariant e n a ha k).le
local notation "I" => rankStageCoreBoundaryIdeal e n a ha J k
local notation "hI" => rankStageCoreBoundaryIdeal_invariant e n a ha J hJ k
local notation "rI" => pullback.snd r (I).subschemeι
local notation "sI" => InvariantIdealRelation.snd I r s hI
local notation "g" => rankStageCoreOriginalBoundaryMap e n a ha J k
local notation "R" => invariants p.appTop.hom q.appTop.hom
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
local notation "f₀" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "f" => rankStageBoundaryOriginalScalars e n a ha J k
local notation "h" => rankStageBoundaryOriginalScalars_condition e n a ha J hJ k
local notation "c" => pullback.lift rI sI h
variable {T : Scheme.{0}}

/-- Both prescribed original endpoints already supply the original scalar equation. -/
theorem rankStage_test_scalar_condition (t : T ⟶ pullback f₀ f₀)
    (x y : T ⟶ (I).subscheme)
    (hx : x ≫ g = t ≫ pullback.fst f₀ f₀)
    (hy : y ≫ g = t ≫ pullback.snd f₀ f₀) : x ≫ f = y ≫ f := by
  unfold rankStageBoundaryOriginalScalars
  rw [← Category.assoc, ← Category.assoc, hx, hy, Category.assoc, Category.assoc,
    pullback.condition]

local notation "hxy" t:max x:max y:max hx:max hy:max =>
  rankStage_test_scalar_condition e n a ha J k t x y hx hy
attribute [local irreducible] rankStageBoundaryOriginalScalars

/-- A full original scheme test lifts exactly when its finite-stage endpoint equations vanish. -/
theorem originalBoundary_test_arrow_iff_stage_endpoint_equations
    (t : T ⟶ pullback f₀ f₀) (x y : T ⟶ (I).subscheme)
    (hx : x ≫ g = t ≫ pullback.fst f₀ f₀)
    (hy : y ≫ g = t ≫ pullback.snd f₀ f₀) :
    (∃ d : T ⟶ pullback p J.subschemeι,
      d ≫ pullback.snd p J.subschemeι = t ≫ pullback.fst f₀ f₀ ∧
      d ≫ InvariantIdealRelation.snd J p q hJ = t ≫ pullback.snd f₀ f₀) ↔
      RingHom.ker (c).appTop.hom ≤
        RingHom.ker (pullback.lift x y (hxy t x y hx hy)).appTop.hom := by
  rw [rankStage_boundary_quotient_iff_original_arrow e n a ha J hJ k x y (hxy t x y hx hy)]
  simp only [hx, hy]

/-- Actual finite-stage equations factor the original test through the full comparison. -/
theorem originalBoundary_test_factor_of_stage_endpoint_equations
    (t : T ⟶ pullback f₀ f₀) (x y : T ⟶ (I).subscheme)
    (hx : x ≫ g = t ≫ pullback.fst f₀ f₀)
    (hy : y ≫ g = t ≫ pullback.snd f₀ f₀)
    (ht : RingHom.ker (c).appTop.hom ≤
      RingHom.ker (pullback.lift x y (hxy t x y hx hy)).appTop.hom) :
    ∃ d : T ⟶ pullback p J.subschemeι,
      d ≫ originalBoundaryComparison p q J hJ = t := by
  obtain ⟨d, hd, hd'⟩ :=
    (originalBoundary_test_arrow_iff_stage_endpoint_equations e n a ha J hJ k t x y hx hy).mpr ht
  refine ⟨d, ?_⟩
  apply (IsPullback.of_hasPullback f₀ f₀).hom_ext
  · simpa only [originalBoundaryComparison, Category.assoc, pullback.lift_fst] using hd
  · simpa only [originalBoundaryComparison, Category.assoc, pullback.lift_snd] using hd'

end FLT.Mazur.EquivalenceRelationOrderedFrames

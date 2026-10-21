/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryFiniteStageTests

/-!
# Sealed full endpoint equations for original scheme tests

The predicate retains the entire endpoint kernel and the two prescribed original
maps. Its exact arrow criterion keeps later field-test statements small to elaborate.
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
local instance sealedEquationOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance sealedEquationOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance sealedEquationOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
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

/-- The full finite-stage equations on an original test with its specified endpoint factors. -/
@[irreducible]
def rankStageOriginalTestEquations (t : T ⟶ pullback f₀ f₀)
    (x y : T ⟶ (I).subscheme)
    (hx : x ≫ g = t ≫ pullback.fst f₀ f₀)
    (hy : y ≫ g = t ≫ pullback.snd f₀ f₀) : Prop :=
  RingHom.ker (c).appTop.hom ≤ RingHom.ker (pullback.lift x y
    (rankStage_test_scalar_condition e n a ha J k t x y hx hy)).appTop.hom

/-- The sealed equations are exactly the original full two-endpoint arrow test. -/
theorem rankStageOriginalTestEquations_iff (t : T ⟶ pullback f₀ f₀)
    (x y : T ⟶ (I).subscheme)
    (hx : x ≫ g = t ≫ pullback.fst f₀ f₀)
    (hy : y ≫ g = t ≫ pullback.snd f₀ f₀) :
    rankStageOriginalTestEquations e n a ha J hJ k t x y hx hy ↔
      ∃ d : T ⟶ pullback p J.subschemeι,
        d ≫ pullback.snd p J.subschemeι = t ≫ pullback.fst f₀ f₀ ∧
        d ≫ InvariantIdealRelation.snd J p q hJ = t ≫ pullback.snd f₀ f₀ := by
  rw [rankStageOriginalTestEquations]
  exact (originalBoundary_test_arrow_iff_stage_endpoint_equations
    e n a ha J hJ k t x y hx hy).symm

/-- Full endpoint equations construct factorization through the original comparison. -/
theorem rankStageOriginalTestEquations_factor (t : T ⟶ pullback f₀ f₀)
    (x y : T ⟶ (I).subscheme)
    (hx : x ≫ g = t ≫ pullback.fst f₀ f₀)
    (hy : y ≫ g = t ≫ pullback.snd f₀ f₀)
    (ht : rankStageOriginalTestEquations e n a ha J hJ k t x y hx hy) :
    ∃ d : T ⟶ pullback p J.subschemeι, d ≫ originalBoundaryComparison p q J hJ = t := by
  rw [rankStageOriginalTestEquations] at ht
  exact originalBoundary_test_factor_of_stage_endpoint_equations
    e n a ha J hJ k t x y hx hy ht

end FLT.Mazur.EquivalenceRelationOrderedFrames

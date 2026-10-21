/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationEndpointQuotientTests
public import FLT.Mazur.OriginalBoundaryResidueArrows
public import FLT.Mazur.RankStageOriginalBoundaryArrows

/-!
# Finite rank-boundary endpoint quotients over original scalars

The actual finite boundary relation is the quotient by its full endpoint
ideal over the unchanged original invariant ring. Killing these equations
constructs an original boundary arrow with both prescribed endpoints.
No assertion of full original scalar-fiber coverage is made.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance quotientOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance quotientOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance quotientOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
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
local instance quotientCore_affine : IsAffine (C).toScheme := rankStageCore_affine e n a ha k
local instance quotientBoundary_affine : IsAffine (I).subscheme :=
  isAffine_of_isAffineHom (I).subschemeι
local instance quotientFirst_finite : IsFinite r := by
  let _ := rankStageFirst_finite (p := p) n k
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- The named core retains its monomorphism into the unchanged original source. -/
instance rankStageCoreOriginalMap_mono : Mono (rankStageCoreOriginalMap e n a ha k) := by
  unfold rankStageCoreOriginalMap rankThickeningMap
  infer_instance

/-- The whole finite core boundary retains the original equivalence operations. -/
def rankStageCoreBoundaryEquivalence : CategoryTheory.EquivalenceRelation rI sI :=
  InvariantIdealRelation.equivalence I hI
    (EquivalenceRelationFiber.invariantRestrictionEquivalence e
      (rankStageCoreOriginalArrow_isPullback e n a ha k)
      (rankStageCoreOriginalArrow_second e n a ha k))

/-- The finite boundary stage is mapped to the unchanged original scalar spectrum. -/
def rankStageBoundaryOriginalScalars : (I).subscheme ⟶ Spec (.of R) := g ≫ f₀

/-- Both entire boundary-stage endpoints obey the original scalar equations. -/
theorem rankStageBoundaryOriginalScalars_condition :
    rI ≫ rankStageBoundaryOriginalScalars e n a ha J k =
      sI ≫ rankStageBoundaryOriginalScalars e n a ha J k := by
  unfold rankStageBoundaryOriginalScalars
  rw [← Category.assoc, ← Category.assoc, ← rankStageOriginalBoundaryArrow_first,
    ← rankStageOriginalBoundaryArrow_second e n a ha J hJ k, Category.assoc,
    Category.assoc, originalBoundary_scalar_condition p q J hJ]

local notation "f" => rankStageBoundaryOriginalScalars e n a ha J k
local notation "h" => rankStageBoundaryOriginalScalars_condition e n a ha J hJ k
local notation "c" => pullback.lift rI sI h
attribute [local irreducible] rankStageBoundaryOriginalScalars

/-- This is an actual full endpoint quotient over original scalars, with all nilpotents. -/
def rankStageBoundaryEndpointQuotientEquiv :
    Γ(pullback f f, ⊤) ⧸ RingHom.ker (c).appTop.hom ≃+* Γ(pullback r (I).subschemeι, ⊤) :=
  FiniteRelationEndpointQuotientTests.endpointQuotientEquiv rI sI f h
    (rankStageCoreBoundaryEquivalence e n a ha J hJ k)

include hJ in
/-- Full finite-stage quotient equations construct an arrow in the original boundary relation. -/
theorem rankStage_original_boundary_arrow_of_quotient {T : Scheme.{0}}
    (x y : T ⟶ (I).subscheme) (hxy : x ≫ f = y ≫ f)
    (ht : RingHom.ker (c).appTop.hom ≤
      RingHom.ker (pullback.lift x y hxy).appTop.hom) :
    ∃ z : T ⟶ pullback p J.subschemeι,
      z ≫ pullback.snd p J.subschemeι = x ≫ g ∧
      z ≫ InvariantIdealRelation.snd J p q hJ = y ≫ g := by
  obtain ⟨d, hd, _⟩ := (FiniteRelationEndpointQuotientTests.existsUnique_arrow_iff rI sI f h
    (rankStageCoreBoundaryEquivalence e n a ha J hJ k) x y hxy).mpr ht
  exact rankStage_original_boundary_arrow_of_stage e n a ha J hJ k x y d hd.1 hd.2

end FLT.Mazur.EquivalenceRelationOrderedFrames

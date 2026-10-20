/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoreBoundaryTransitions

/-!
# Full boundary invariant coefficients on fixed rank-stage cores

The exact original ideal restricts to an invariant ideal on each named affine
core. Its full boundary coefficient ring keeps these domains
fixed, so prescribed boundary data can be compared across orders.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance boundaryCoeffOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance boundaryCoeffOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance boundaryCoeffOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q) (k : ℕ)
set_option quotPrecheck false
local notation "U" => rankStageCore e n a ha k
local notation "hU" => rankStageCore_invariant e n a ha k
local notation "r" => (rankStageFirst (p := p) n k).resLE U _ le_rfl
local notation "s" => (rankStageSecond e n k).resLE U _ (hU).le
local notation "I" => rankStageCoreBoundaryIdeal e n a ha J k

include hJ in
/-- The entire original ideal remains invariant on the actual named affine domain. -/
theorem rankStageCoreBoundaryIdeal_invariant : (I).comap r = (I).comap s :=
  FiniteEtaleInvariantOpenBoundary.ideal_invariant _ _ U hU
    (rankStageBoundaryIdeal (p := p) n k J) (rankStageBoundaryIdeal_invariant e n k J hJ)

/-- The full endpoint equalizer on the exact original boundary of a named core. -/
abbrev rankStageCoreBoundaryInvariants := compatibleFunctions (pullback.snd r (I).subschemeι)
  (InvariantIdealRelation.snd I r s (rankStageCoreBoundaryIdeal_invariant e n a ha J hJ k))

end FLT.Mazur.EquivalenceRelationOrderedFrames

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationRankThickening

/-!
# The unchanged boundary ideal on each full rank-stage relation

Any original invariant boundary ideal pulls back to an exactly invariant
ideal on every infinitesimal rank stage. Its closed relation is the entire
first-endpoint pullback and remains finite and etale.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A]
  (e : CategoryTheory.EquivalenceRelation p q) (n k : ℕ)
local instance rankBoundaryOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance rankBoundaryOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance rankBoundaryOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local notation "b" => rankThickeningMap (Over.mk p) n k
local notation "r" => rankStageFirst (p := p) n k
local notation "s" => rankStageSecond e n k
local notation "a" => rankStageArrow (p := p) n k
variable (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)

/-- Pullback retains the complete original boundary equations on the rank stage. -/
def rankStageBoundaryIdeal : (rankThickening (Over.mk p) n k).IdealSheafData := J.comap b

include hJ in
/-- Both independent full endpoints pull back exactly the same original boundary ideal. -/
theorem rankStageBoundaryIdeal_invariant :
    (rankStageBoundaryIdeal (p := p) n k J).comap r =
      (rankStageBoundaryIdeal (p := p) n k J).comap s := by
  unfold rankStageBoundaryIdeal
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    ← (rankStageFirst_isPullback (p := p) n k).w, rankStageSecond_map,
    Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hJ]

set_option quotPrecheck false
local notation "I" => rankStageBoundaryIdeal (p := p) n k J
local notation "j" => (I).subschemeι

/-- The full second endpoint on the actual pulled original boundary. -/
def rankStageBoundarySecond : pullback r j ⟶ (I).subscheme :=
  InvariantIdealRelation.snd I r s (rankStageBoundaryIdeal_invariant e n k J hJ)

/-- The actual boundary retains the full rank-stage equivalence relation. -/
def rankStageBoundaryEquivalence : CategoryTheory.EquivalenceRelation
    (pullback.snd r j) (rankStageBoundarySecond e n k J hJ) :=
  InvariantIdealRelation.equivalence I (rankStageBoundaryIdeal_invariant e n k J hJ)
    (rankStageEquivalence e n k)

instance rankStageBoundaryFirst_etale : Etale (pullback.snd r j) := inferInstance

instance rankStageBoundarySecond_etale : Etale (rankStageBoundarySecond e n k J hJ) := by
  unfold rankStageBoundarySecond
  infer_instance

variable [LocallyQuasiFinite p]

omit [Etale q] [IsLocallyNoetherian A] in
/-- The entire original boundary relation is finite on every rank stage. -/
theorem rankStageBoundaryFirst_finite : IsFinite (pullback.snd r j) := by
  let _ := rankStageFirst_finite (p := p) n k
  infer_instance

end FLT.Mazur.EquivalenceRelationOrderedFrames

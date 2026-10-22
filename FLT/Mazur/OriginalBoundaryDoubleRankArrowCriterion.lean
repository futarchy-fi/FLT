/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryDoubleRankComparison
public import FLT.Mazur.RelativeDiagonalRankDetection

/-!
# Exact original arrows from diagonal stages and the rank obstruction

On an affine Noetherian coefficient test with finite full first source,
original arrows are equivalent to two separate requirements: absence of
rank collisions and arrows on every diagonal two-order thickening. The
closed comparison and all-order detection construct the full arrow; no
flat descent property of the rank stages is used or assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A}
  [IsAffine A] [IsNoetherian A] [IsSeparated p] [Etale p] [QuasiCompact p]
  [IsAffine B] [IsLocallyNoetherian B]
  (J : A.IdealSheafData) (e : CategoryTheory.EquivalenceRelation p q)
  (hJ : J.comap p = J.comap q)
local instance doubleArrowOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance doubleArrowOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance doubleArrowOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "c" => originalBoundaryComparison p q J hJ
include e

/-- A full original arrow is constructed from all independent rank orders of a finite test. -/
theorem originalBoundary_unique_lift_of_doubleRank
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : ∀ n m r s : ℕ,
      ∃ d : doubleRankThickening (Over.mk p) (t ≫ x) (t ≫ y) n m r s ⟶
        pullback p J.subschemeι,
      d ≫ c = doubleRankMap (Over.mk p) (t ≫ x) (t ≫ y) n m r s ≫ t) :
    ∃! d : B ⟶ pullback p J.subschemeι, d ≫ c = t := by
  let _ := originalBoundaryComparison_mono e J hJ
  let _ := originalBoundary_comparison_test_closedImmersion J hJ t e
  exact existsUnique_lift_of_doubleRank (Over.mk p) (t ≫ x) (t ≫ y) c t h

/-- Neither off-diagonal emptiness nor full diagonal equations are hidden in a cover assumption. -/
theorem originalBoundary_unique_lift_iff_diagonalRank
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))] :
    (∃! d : B ⟶ pullback p J.subschemeι, d ≫ c = t) ↔
      (∀ z : B, ∃ n, x (t z) ∈ exactRank (Over.mk p) n ∧
        y (t z) ∈ exactRank (Over.mk p) n) ∧
      (∀ n r s : ℕ,
        ∃ d : doubleRankThickening (Over.mk p) (t ≫ x) (t ≫ y) n n r s ⟶
          pullback p J.subschemeι,
        d ≫ c = doubleRankMap (Over.mk p) (t ≫ x) (t ≫ y) n n r s ≫ t) := by
  constructor
  · rintro ⟨d, hd, _⟩
    constructor
    · intro z
      apply (not_mem_rankCollision_iff (Over.mk p) x y (t z)).mp
      apply originalBoundary_comparison_not_rankCollision J e hJ
      exact ⟨d z, congrArg (fun a : B ⟶ pullback f f ↦ a z) hd⟩
    · intro n r s
      refine ⟨doubleRankMap (Over.mk p) (t ≫ x) (t ≫ y) n n r s ≫ d, ?_⟩
      rw [Category.assoc, hd]
  · rintro ⟨hr, hl⟩
    let _ := originalBoundaryComparison_mono e J hJ
    let _ := originalBoundary_comparison_test_closedImmersion J hJ t e
    exact existsUnique_lift_of_diagonalRank (Over.mk p) (t ≫ x) (t ≫ y) hr c t hl

/-- Full boundary invariant coefficients agree on the resulting entire nonreduced test. -/
theorem originalBoundary_invariant_eq_of_doubleRank
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : ∀ n m r s : ℕ,
      ∃ d : doubleRankThickening (Over.mk p) (t ≫ x) (t ≫ y) n m r s ⟶
        pullback p J.subschemeι,
      d ≫ c = doubleRankMap (Over.mk p) (t ≫ x) (t ≫ y) n m r s ≫ t)
    (a : SchemeEffectiveEpiSections.compatibleFunctions
      (pullback.snd p J.subschemeι) (InvariantIdealRelation.snd J p q hJ)) :
    (t ≫ pullback.fst f f).appTop a.val = (t ≫ pullback.snd f f).appTop a.val := by
  obtain ⟨d, hd, _⟩ := originalBoundary_unique_lift_of_doubleRank J e hJ t h
  rw [← hd]
  simp only [Category.assoc, originalBoundaryComparison, pullback.lift_fst,
    pullback.lift_snd, Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply]
  exact congrArg (fun b ↦ d.appTop b) a.property

end FLT.Mazur.EquivalenceRelationOrderedFrames

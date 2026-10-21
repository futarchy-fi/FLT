/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageRelativeClosedCoreObstruction
public import FLT.Mazur.RankStageOriginalBoundaryScalarObstruction

/-!
# Original core products with relatively closed higher ranks

For a finite family of arbitrary original chart parameters, original
invariant scalars defining their cores have a product annihilating the
whole compatible homogeneous error family. Higher ranks need only be
closed in each current rank open; the original projection need not be finite.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance relativeProductOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance relativeProductOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance relativeProductOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable {S : Scheme.{0}} [IsAffine S] (f : A ⟶ S)
  (hf : p ≫ f = q ≫ f) [IsSeparated f]
  {ι : Type*} [Fintype ι] (n : ι → ℕ)
  (a : ι → Γ(A, ⊤))
  (hs : ∀ j, A.basicOpen (a j) ≤ rankImageOpen (Over.mk p) (n j))
  (hn : ∀ j, IsClosed ((rankImageOpen (Over.mk p) (n j)).ι ⁻¹'
    (rankImageOpen (Over.mk p) (n j + 1) : Set A)))
  (s : ι → compatibleFunctions p q)
  (hcore : ∀ j k, rankStageCore e (n j) (a j) (hs j) k =
    (rankThickening (Over.mk p) (n j) k).basicOpen
      (rankStageOriginalInvariantRestriction e (n j) k (s j)).val)
  (J : A.IdealSheafData)
  (x : ∀ j, rankStageCompatibleCoreInvariants e (n j) (a j) (hs j))
  (hx : ∀ j k, (rankStageCoreBoundaryIdeal e (n j) (a j) (hs j) J k).subschemeι.appTop
    ((x j).val k).val = 0)
attribute [local irreducible] rankStageCore rankStageOriginalNumeratorIdeal
  rankStageCompatibleNumeratorIdeal rankStageOriginalCompatibleScalars

include hf hn hcore hx in
/-- A constructed product in the unchanged scalar ring kills every full selected obstruction. -/
theorem rankStageOriginalCoreProduct_mem_radical_of_next_relatively_closed :
    (∏ j, s j) ∈
      (rankStageFamilyNumeratorIdeal e n a hs J x).radical := by
  classical
  apply (FiniteScalarObstruction.mem_radical_jointIdeal _ _).mpr
  intro j
  have hj := rankStageOriginalCoreScalar_mem_radical_of_next_relatively_closed
    e (n j) (hn j) J f hf (a j) (hs j) (s j) (x j) (hx j) (hcore j)
  obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem
    (fun j ↦ s j) (Finset.mem_univ j)
  rw [hb]
  exact Ideal.mul_mem_right _ _ hj

include hf hn hcore hx in
/-- One exponent in the original ring gives ordinary compatible full homogeneous numerators. -/
theorem exists_rankStageOriginalCoreProduct_uniform_of_next_relatively_closed :
    ∃ (N : ℕ) (w : ∀ j k, rankStageInvariants e (n j) k),
      (∀ j k, w j k ∈ rankStageGlobalBoundaryKernel e (n j) J k) ∧
      (∀ j k l (h : k ≤ l), rankStageInvariantTransition e (n j) h (w j l) = w j k) ∧
      ∀ j k, rankStageGlobalCoreRestriction e (n j) (a j) (hs j) k (w j k) =
        (rankStageGlobalCoreRestriction e (n j) (a j) (hs j) k
          (rankStageOriginalInvariantRestriction e (n j) k
            (∏ j, s j))) ^ N *
            (x j).val k := by
  apply exists_rankStage_family_uniform_numerators e n a hs J x (∏ j, s j)
  exact (FiniteScalarObstruction.mem_radical_jointIdeal _ _).mp
    (rankStageOriginalCoreProduct_mem_radical_of_next_relatively_closed
      e f hf n a hs hn s hcore J x hx)

end FLT.Mazur.EquivalenceRelationOrderedFrames

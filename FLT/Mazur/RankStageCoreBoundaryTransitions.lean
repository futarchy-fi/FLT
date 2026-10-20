/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCompatibleCoreCoefficients
public import FLT.Mazur.IdealSheafClosedTransitions
public import FLT.Mazur.RankStageAffineBoundaryLifts

/-!
# Exact boundary transitions on coherent rank-stage affine cores

The unchanged original boundary ideal pulls back along each actual domain
map. Its closed subscheme transitions commute with function restriction.
Compatible full invariant coefficients therefore give compatible full boundary
coefficients; this does not prescribe the higher-order boundary values.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance coreBoundaryOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance coreBoundaryOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance coreBoundaryOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData)
local notation "U" => rankStageCore e n a ha
local notation "C" => rankStageCoreInvariants e n a ha

/-- The full original boundary ideal on the fixed affine domain at each order. -/
def rankStageCoreBoundaryIdeal (k : ℕ) : (U k).toScheme.IdealSheafData :=
  (rankStageBoundaryIdeal (p := p) n k J).comap (U k).ι

/-- The complete original boundary equations commute with the actual domain transition. -/
theorem rankStageCoreBoundaryIdeal_transition {k l : ℕ} (h : k ≤ l) :
    (rankStageCoreBoundaryIdeal e n a ha J l).comap (rankStageCoreMap e n a ha h) =
      rankStageCoreBoundaryIdeal e n a ha J k := by
  unfold rankStageCoreBoundaryIdeal rankStageBoundaryIdeal
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    rankStageCoreMap_inclusion, Category.assoc, rankStageTransition_map,
    Scheme.IdealSheafData.comap_comp]

/-- The actual closed boundary map between the named affine domains. -/
def rankStageCoreBoundaryMap {k l : ℕ} (h : k ≤ l) :
    (rankStageCoreBoundaryIdeal e n a ha J k).subscheme ⟶
      (rankStageCoreBoundaryIdeal e n a ha J l).subscheme :=
  IdealSheafClosedTransitions.map _ _ (rankStageCoreMap e n a ha h)
    (rankStageCoreBoundaryIdeal_transition e n a ha J h)

/-- Boundary coefficients of compatible invariants agree on the whole closed subscheme. -/
theorem rankStageCoreBoundary_compatible {k l : ℕ} (h : k ≤ l) (v : C k) (w : C l)
    (hv : rankStageCoreRestriction e n a ha h w = v) :
    (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop v.val =
      (rankStageCoreBoundaryMap e n a ha J h).appTop
        ((rankStageCoreBoundaryIdeal e n a ha J l).subschemeι.appTop w.val) := by
  rw [← hv, rankStageCoreRestriction_val]
  exact IdealSheafClosedTransitions.section_square _ _ _ _ w.val

variable {S : Scheme.{0}} [IsAffine S] (f : A ⟶ S)
  (hf : p ≫ f = q ≫ f) [IsSeparated f]

include hf in
/-- Every initial invariant extends with genuinely compatible full boundary restrictions. -/
theorem exists_compatible_rankStageCore_boundary_restrictions (z : C 0) :
    ∃ v : ∀ k : ℕ, C k, v 0 = z ∧
      (∀ k l (h : k ≤ l), rankStageCoreRestriction e n a ha h (v l) = v k) ∧
      ∀ k l (h : k ≤ l),
        (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop (v k).val =
          (rankStageCoreBoundaryMap e n a ha J h).appTop
            ((rankStageCoreBoundaryIdeal e n a ha J l).subschemeι.appTop (v l).val) := by
  obtain ⟨v, hv, hc⟩ := exists_compatible_rankStageCore_coefficients e n a ha f hf z
  exact ⟨v, hv, hc, fun k l h ↦ rankStageCoreBoundary_compatible e n a ha J h
    (v k) (v l) (hc k l h)⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames

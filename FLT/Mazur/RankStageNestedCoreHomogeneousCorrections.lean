/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageInvariantOverlapCocycle
public import FLT.Mazur.RankStageOriginalBoundaryTower

/-!
# All-order homogeneous splitting inside one actual rank core

Construct a boundary tower on the containing core, then subtract its
restrictions from independently supplied towers on smaller cores. These
are actual boundary-zero corrections on the whole smaller cores, compatible
at every order, and they kill the original product-core errors. The result
does not supply a containing core for an arbitrary finite stage cover.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance nestedCoreOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance nestedCoreOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance nestedCoreOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  {ι : Type*} (b : ι → Γ(A, ⊤))
  (hb : ∀ j, A.basicOpen (b j) ≤ rankImageOpen (Over.mk p) n)
  (h : ∀ j k, rankStageCore e n (b j) (hb j) k ≤ rankStageCore e n a ha k)
local notation "C" j:max k:max => rankStageCore e n (b j) (hb j) k
local notation "I" j:max k:max => rankStageCoreBoundaryIdeal e n (b j) (hb j) J k
local notation "R" j:max k:max => rankStageCoreRefinement e n a (b j) ha (hb j) k (h j k)
attribute [local irreducible] rankStageCore

include h hf in
/-- A containing affine core supplies homogeneous corrections compatible at all orders. -/
theorem exists_rankStage_nested_core_corrections
    (t : compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ))
    (v : ∀ j k, rankStageCoreInvariants e n (b j) (hb j) k)
    (hv : ∀ j k, (I j k).subschemeι.appTop (v j k).val =
      (rankStageCoreOriginalBoundaryMap e n (b j) (hb j) J k).appTop t.val)
    (ht : ∀ j k l (hkl : k ≤ l),
      rankStageCoreRestriction e n (b j) (hb j) hkl (v j l) = v j k) :
    ∃ c : ∀ j k, rankStageCoreInvariants e n (b j) (hb j) k,
      (∀ j k, (I j k).subschemeι.appTop (c j k).val = 0) ∧
      (∀ j k l (hkl : k ≤ l),
        rankStageCoreRestriction e n (b j) (hb j) hkl (c j l) = c j k) ∧
      ∀ j d k, rankStageInvariantOverlapError e n (b j) (b d) (hb j) (hb d) k
        (v j k - c j k) (v d k - c d k) = 0 := by
  obtain ⟨w, hw, hwc⟩ := exists_rankStage_original_boundary_tower e n a ha J hJ f hf t
  let c (j : ι) (k : ℕ) := v j k - (R j k) (w k)
  have hc (j : ι) (k : ℕ) : v j k - c j k = (R j k) (w k) := sub_sub_cancel _ _
  refine ⟨c, ?_, ?_, ?_⟩
  · intro j k
    let _ : IsAffine (C j k).toScheme := rankStageCore_affine e n (b j) (hb j) k
    have he := rankStage_distinct_core_boundary_difference e n k (b j) a (hb j) ha J
      (𝟙 (C j k).toScheme) ((rankThickening (Over.mk p) n k).homOfLE (h j k))
      (by rw [Category.id_comp, rankStageCoreRefinement_original])
      (v j k) (w k) t.val (hv j k) (hw k)
    rw [Category.id_comp, rankStageCoreOriginalMap_ideal] at he
    rw [← (I j k).ker_subschemeι_app ⟨⊤, isAffineOpen_top _⟩] at he
    simp only [Scheme.Hom.id_appTop, CommRingCat.id_apply] at he
    change (I j k).subschemeι.appTop ((v j k).val -
      ((rankThickening (Over.mk p) n k).homOfLE (h j k)).appTop (w k).val) = 0 at he
    change (I j k).subschemeι.appTop ((v j k).val - ((R j k) (w k)).val) = 0
    rw [rankStageCoreRefinement_val]
    exact he
  · intro j k l hkl
    change rankStageCoreRestriction e n (b j) (hb j) hkl
      (v j l - (R j l) (w l)) = v j k - (R j k) (w k)
    rw [map_sub, ht, rankStageCoreRefinement_transition, hwc]
  · intro j d k
    rw [hc, hc]
    simp only [rankStageInvariantOverlapError, rankStageCoreRefinement_comp, sub_self]

end FLT.Mazur.EquivalenceRelationOrderedFrames

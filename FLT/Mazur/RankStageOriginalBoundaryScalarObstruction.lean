/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOverlapScalarObstruction
public import FLT.Mazur.RankStageOriginalBoundaryTower

/-!
# A constructed all-order scalar obstruction from the original boundary

The original invariant boundary section constructs the local compatible
towers, hence their actual finite overlap obstruction over original scalars.
No local tower or correction is supplied as an extra hypothesis. Vanishing
of this particular cyclic module would give compatible unscaled global
homogeneous overlap extensions; cocycle splitting and algebraization remain.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance boundaryScalarOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance boundaryScalarOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance boundaryScalarOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : compatibleFunctions (pullback.snd p J.subschemeι) (InvariantIdealRelation.snd J p q hJ))

/-- Choose an actual full boundary lift tower using the already proved geometric lifting theorem. -/
def rankStageChosenBoundaryCoreTower : rankStageCompatibleCoreInvariants e n a ha :=
  ⟨(exists_rankStage_original_boundary_tower e n a ha J hJ f hf t).choose,
    (exists_rankStage_original_boundary_tower e n a ha J hJ f hf t).choose_spec.2⟩

/-- The chosen tower retains the unchanged original boundary section, including nilpotents. -/
theorem rankStageChosenBoundaryCoreTower_boundary (k : ℕ) :
    (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop
        ((rankStageChosenBoundaryCoreTower e n a ha J hJ f hf t).val k).val =
      (rankStageCoreOriginalBoundaryMap e n a ha J k).appTop t.val :=
  (exists_rankStage_original_boundary_tower e n a ha J hJ f hf t).choose_spec.1 k

variable {ι : Type*} (c : ι → Γ(A, ⊤))
  (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
local notation "v" j:max => rankStageChosenBoundaryCoreTower e n (c j) (hc j) J hJ f hf t
attribute [local irreducible] rankStageChosenBoundaryCoreTower

/-- The exact original-scalar ideal is now constructed from the original boundary data alone. -/
def rankStageOriginalBoundaryOverlapIdeal : Ideal (compatibleFunctions p q) :=
  rankStageOverlapNumeratorIdeal e n c hc J (fun j ↦ v j)

/-- The selected complete overlap error vector has a finite original-scalar obstruction module. -/
theorem rankStageOriginalBoundaryOverlapQuotient_finite :
    Module.Finite (compatibleFunctions p q)
      ((compatibleFunctions p q) ⧸ rankStageOriginalBoundaryOverlapIdeal e n J hJ f hf t c hc) :=
  inferInstance

/-- Every constructed overlap error is homogeneous on the full pulled original boundary. -/
theorem rankStageOriginalBoundaryOverlap_error_zero (i j : ι) (k : ℕ) :
    (rankStageCoreBoundaryIdeal e n (c i * c j)
      (rankStageProduct_domain n (c i) (c j) (hc i)) J k).subschemeι.appTop
        ((rankStageCompatibleOverlapError e n (c i) (c j) (hc i) (hc j)
          (v i) (v j)).val k).val = 0 :=
  rankStageCompatibleOverlapError_boundary_zero e n (c i) (c j) (hc i) (hc j)
    (v i) (v j) J t.val
    (rankStageChosenBoundaryCoreTower_boundary e n (c i) (hc i) J hJ f hf t)
    (rankStageChosenBoundaryCoreTower_boundary e n (c j) (hc j) J hJ f hf t) k

/-- Unit membership is precisely compatible unscaled extension of the constructed overlap errors. -/
theorem one_mem_rankStageOriginalBoundaryOverlapIdeal :
    1 ∈ rankStageOriginalBoundaryOverlapIdeal e n J hJ f hf t c hc ↔
      ∃ w : ∀ _ : ι × ι, ∀ k, rankStageInvariants e n k,
        (∀ j k, w j k ∈ rankStageGlobalBoundaryKernel e n J k) ∧
        (∀ j k l (h : k ≤ l), rankStageInvariantTransition e n h (w j l) = w j k) ∧
        ∀ j k, rankStageGlobalCoreRestriction e n (c j.1 * c j.2)
            (rankStageProduct_domain n (c j.1) (c j.2) (hc j.1)) k (w j k) =
          rankStageInvariantOverlapError e n (c j.1) (c j.2) (hc j.1) (hc j.2) k
            ((v j.1).val k) ((v j.2).val k) :=
  one_mem_rankStageOverlapNumeratorIdeal e n c hc J (fun j ↦ v j)

end FLT.Mazur.EquivalenceRelationOrderedFrames

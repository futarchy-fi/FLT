/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteCharacterLifts
public import FLT.Mazur.EquivalenceRelationCompleteBoundaryCorrections
public import FLT.Mazur.SchemeFiniteGroupFreeFlat

/-!
# Finite flat complete frames over powers of the orbit ideal

Pull the original affine frame chart back to the actual quotient by each
positive power of the complete-orbit ideal. These finite flat covers preserve
all stage coefficients and have complete support, without a cutoff change.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
local notation "ρ" => restrictedAction (action e I o) U hU
local notation "J" => completeAffineOrbitIdeal e I o U hU

/-- The actual invariant-coordinate quotient at a positive ideal-power order. -/
def completeQuotientStage (k : ℕ) : Scheme :=
  Spec (.of (invariantCoordinates ρ ⧸ J ^ (k + 1)))

/-- Retain the full closed immersion into the original invariant quotient. -/
def completeQuotientStageMap (k : ℕ) : completeQuotientStage e I o U hU k ⟶ quotient ρ :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (k + 1))))

instance completeQuotientStageMap_closed (k : ℕ) :
    IsClosedImmersion (completeQuotientStageMap e I o U hU k) := by
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- Every positive quotient order has precisely the complete-orbit support. -/
theorem completeQuotientStageMap_range (k : ℕ) :
    Set.range (completeQuotientStageMap e I o U hU k) =
      (completeAffineOrbitImage e I o U hU : Set (quotient ρ)) := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (J ^ (k + 1)))) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, PrimeSpectrum.zeroLocus_pow _ (Nat.succ_ne_zero k),
    completeAffineOrbitIdeal_zeroLocus]

/-- The original frame chart pulled back to the full power quotient. -/
abbrev completeQuotientFrame (k : ℕ) : Scheme :=
  pullback (quotientMap ρ) (completeQuotientStageMap e I o U hU k)

/-- The cover of the full coefficient stage, not of its reduction. -/
abbrev completeQuotientFrameCover (k : ℕ) : completeQuotientFrame e I o U hU k ⟶
    completeQuotientStage e I o U hU k := pullback.snd _ _

/-- The unchanged original normalized-frame map. -/
def completeQuotientFrameInclusion (k : ℕ) :
    completeQuotientFrame e I o U hU k ⟶ source p q I o := pullback.fst _ _ ≫ U.ι

instance completeQuotientFrameInclusion_mono (k : ℕ) :
    Mono (completeQuotientFrameInclusion e I o U hU k) := by
  unfold completeQuotientFrameInclusion
  infer_instance

instance completeQuotientFrame_affine (k : ℕ) :
    IsAffine (completeQuotientFrame e I o U hU k) := by
  exact isAffine_of_isAffineHom
    (pullback.fst (quotientMap ρ) (completeQuotientStageMap e I o U hU k))

/-- Every frame on this constructed nonreduced cover is complete. -/
theorem completeQuotientFrame_complete (k : ℕ) :
    Set.range (completeQuotientFrameInclusion e I o U hU k) ⊆
      completePointLocus (p := p) (q := q) I o := by
  rintro _ ⟨x, rfl⟩
  change pullback.fst (quotientMap ρ) (completeQuotientStageMap e I o U hU k) x ∈
    U.ι ⁻¹' completePointLocus (p := p) (q := q) I o
  rw [← completeAffineOrbitImage_preimage e I o U hU]
  change quotientMap ρ
    (pullback.fst (quotientMap ρ) (completeQuotientStageMap e I o U hU k) x) ∈
      (completeAffineOrbitImage e I o U hU : Set (quotient ρ))
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  exact (completeQuotientStageMap_range e I o U hU k).le ⟨_, rfl⟩

/-- The original moving action persists on every full quotient stage. -/
def completeQuotientFrameAction (k : ℕ) :
    Equiv.Perm I →* Aut (completeQuotientFrame e I o U hU k) :=
  FiniteGroupPullback.action ρ (quotientMap ρ) (quotientMap_invariant ρ)
    (completeQuotientStageMap e I o U hU k)

/-- Equivariance retains the full original normalized source morphism. -/
@[reassoc] theorem completeQuotientFrameAction_inclusion (k : ℕ) (g : Equiv.Perm I) :
    (completeQuotientFrameAction e I o U hU k g).hom ≫
      completeQuotientFrameInclusion e I o U hU k =
    completeQuotientFrameInclusion e I o U hU k ≫ (action e I o g).hom := by
  unfold completeQuotientFrameAction completeQuotientFrameInclusion
  rw [FiniteGroupPullback.action_fst_assoc, Category.assoc, restrictedAction_hom_ι]

omit [Etale p] [IsAffine U.toScheme] in
private theorem stageAction_free (K : Type) [Field K]
    (a : Spec (.of K) ⟶ U.toScheme) (g : Equiv.Perm I)
    (ha : a ≫ (ρ g).hom = a) : g = 1 :=
  restrictedAction_free (action e I o) U hU
    (fun _ _ b g hb ↦ action_free e I o b g hb) K a g ha

/-- The constructed complete cover is finite at every positive power order. -/
instance completeQuotientFrameCover_finite (k : ℕ) :
    IsFinite (completeQuotientFrameCover e I o U hU k) := by
  let _ := quotientMap_finite_of_free ρ (stageAction_free e I o U hU)
  infer_instance

/-- All nilpotent coefficient directions are retained by a flat cover. -/
instance completeQuotientFrameCover_flat (k : ℕ) :
    Flat (completeQuotientFrameCover e I o U hU k) := by
  let _ := quotientMap_flat_of_free ρ (stageAction_free e I o U hU)
  infer_instance

/-- Every point of the quotient stage has an actual original complete frame above it. -/
instance completeQuotientFrameCover_surjective (k : ℕ) :
    Surjective (completeQuotientFrameCover e I o U hU k) := by infer_instance

/-- The finite flat cover gives effective descent of the entire coefficient stage. -/
instance completeQuotientFrameCover_effectiveEpi (k : ℕ) :
    EffectiveEpi (completeQuotientFrameCover e I o U hU k) := by infer_instance

end FLT.Mazur.EquivalenceRelationNormalizedFrames

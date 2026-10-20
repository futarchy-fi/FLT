/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalStepSmoothOpen

/-!
# Embed the preceding smooth model in the successor smooth model

The inverse of the full unchanged-open comparison preserves the actual step
contraction. Smoothness of the lifted open follows from its unchanged structure
map, so the result is an open immersion between the two entire smooth loci.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j + 1 ≤ n)
local notation "base" => finiteGlobalStructure hπ data j (Nat.le_of_succ_le hj)
local notation "next" => finiteGlobalStructure hπ data (j + 1) hj
local notation "U" => (base).smoothLocus
local notation "V" => (next).smoothLocus

/-- The preceding entire smooth locus lifted into the actual successor model. -/
def finiteGlobalStepSmoothLift : (U).toScheme ⟶ finiteGlobalModel hπ data (j + 1) hj :=
  SchemeUnchangedOpen.lift (finiteGlobalStep hπ data j hj) (U).ι (by
    rw [Scheme.Opens.opensRange_ι]
    exact finiteGlobalStep_smooth_isIso hπ data j hj)

instance finiteGlobalStepSmoothLift_open :
    IsOpenImmersion (finiteGlobalStepSmoothLift hπ data j hj) := by
  unfold finiteGlobalStepSmoothLift
  infer_instance

/-- The lift retains the whole preceding smooth inclusion after the actual step. -/
@[reassoc] theorem finiteGlobalStepSmoothLift_step :
    finiteGlobalStepSmoothLift hπ data j hj ≫ finiteGlobalStep hπ data j hj = (U).ι :=
  SchemeUnchangedOpen.lift_comp _ _ _

/-- The smooth lift is the full inverse image of the preceding smooth open. -/
theorem finiteGlobalStepSmoothLift_isPullback :
    IsPullback (𝟙 _) (finiteGlobalStepSmoothLift hπ data j hj)
      (U).ι (finiteGlobalStep hπ data j hj) :=
  SchemeUnchangedOpen.lift_isPullback _ _ _

/-- The lifted open retains precisely the preceding coefficient structure. -/
@[reassoc] theorem finiteGlobalStepSmoothLift_structure :
    finiteGlobalStepSmoothLift hπ data j hj ≫ next = (U).ι ≫ base := by
  rw [← finiteGlobalStep_structure hπ data j hj, finiteGlobalStepSmoothLift_step_assoc]

/-- Every point of the lifted open is relatively smooth in the successor. -/
theorem finiteGlobalStepSmoothLift_range_smooth :
    Set.range (finiteGlobalStepSmoothLift hπ data j hj) ⊆ V := by
  let _ : Smooth (finiteGlobalStepSmoothLift hπ data j hj ≫ next) := by
    rw [finiteGlobalStepSmoothLift_structure]
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    ext p
    exact iff_of_true p.property (Set.mem_univ p)
  rintro _ ⟨p, rfl⟩
  have h := Scheme.Hom.preimage_smoothLocus_eq (finiteGlobalStepSmoothLift hπ data j hj) next
  rw [Scheme.Hom.smoothLocus_eq_top (finiteGlobalStepSmoothLift hπ data j hj ≫ next)] at h
  exact h.ge (Set.mem_univ p)

/-- The full preceding smooth model embeds in the full successor smooth model. -/
def finiteGlobalStepSmoothEmbedding : (U).toScheme ⟶ (V).toScheme :=
  IsOpenImmersion.lift (V).ι (finiteGlobalStepSmoothLift hπ data j hj) (by
    rw [Scheme.Opens.range_ι]
    exact finiteGlobalStepSmoothLift_range_smooth hπ data j hj)

instance finiteGlobalStepSmoothEmbedding_open :
    IsOpenImmersion (finiteGlobalStepSmoothEmbedding hπ data j hj) := by
  unfold finiteGlobalStepSmoothEmbedding
  infer_instance

/-- Factoring through the successor smooth open retains the actual lift. -/
@[reassoc] theorem finiteGlobalStepSmoothEmbedding_inclusion :
    finiteGlobalStepSmoothEmbedding hπ data j hj ≫ (V).ι =
      finiteGlobalStepSmoothLift hπ data j hj := IsOpenImmersion.lift_fac _ _ _

/-- The smooth-stage embedding contracts to the original preceding smooth inclusion. -/
@[reassoc] theorem finiteGlobalStepSmoothEmbedding_step :
    finiteGlobalStepSmoothEmbedding hπ data j hj ≫ (V).ι ≫
      finiteGlobalStep hπ data j hj = (U).ι := by
  rw [finiteGlobalStepSmoothEmbedding_inclusion_assoc, finiteGlobalStepSmoothLift_step]

/-- The smooth-stage embedding is over the original coefficient scheme. -/
@[reassoc] theorem finiteGlobalStepSmoothEmbedding_structure :
    finiteGlobalStepSmoothEmbedding hπ data j hj ≫ (V).ι ≫ next = (U).ι ≫ base := by
  rw [finiteGlobalStepSmoothEmbedding_inclusion_assoc, finiteGlobalStepSmoothLift_structure]

end FLT.Mazur.WeierstrassDividedDepth

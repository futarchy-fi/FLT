/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteStageClosedCompatibility
public import FLT.Mazur.PolygonInfinitesimalStageEdges
public import FLT.Mazur.PolygonCompletePointIdentityClosedTorus

/-!
# Full Laurent coordinates on the original identity open at every finite order

The unchanged complete-family identity open pulls back to exactly the full
Laurent edge in each original stage. This identifies the actual finite-order
identity parameter, retaining all coefficients and nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj completeClosedFiberInclusion
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "U" => completePointIdentityOpen K n h i
local notation "p" m => originalStageToCompatibleProj K n h m
local notation "e" m => edge (Ring K m) (parameter K m) n h i

/-- The original full identity open has exactly the full Laurent edge as each finite stage. -/
theorem completePointIdentityOpen_stage_preimage (m : ℕ) :
    (p m) ⁻¹ᵁ (U) = (e m).opensRange := by
  ext x
  obtain ⟨z, rfl⟩ := (specialFiberInclusion K m n h).surjective x
  change z ∈ specialFiberInclusion K m n h ⁻¹ᵁ ((p m) ⁻¹ᵁ (U)) ↔ _
  rw [specialFiber_preimage_originalStage, completePointIdentityOpen_closed_preimage]
  exact Set.ext_iff.mp (CartesianFiniteFibers.range_eq_preimage
    (originalTorus_stageEdge_isPullback K n h i m)) z

/-- The full stage Laurent parameter maps into the actual original identity open. -/
def completeIdentityStageTorus (m : ℕ) :
    PolygonSmoothing.branchTorus (Ring K m) ⟶ (U).toScheme :=
  IsOpenImmersion.lift (U).ι ((e m) ≫ (p m)) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change (e m) x ∈ (p m) ⁻¹ᵁ (U)
    rw [completePointIdentityOpen_stage_preimage]
    exact ⟨x, rfl⟩)

/-- Its inclusion is the original full edge followed by the original stage realization. -/
@[reassoc] theorem completeIdentityStageTorus_inclusion (m : ℕ) :
    completeIdentityStageTorus K n h i m ≫ (U).ι = (e m) ≫ (p m) :=
  IsOpenImmersion.lift_fac _ _ _

/-- These are the actual finite identity charts, with their original open inclusions. -/
theorem completeIdentityStageTorus_isPullback (m : ℕ) :
    IsPullback (completeIdentityStageTorus K n h i m) (e m) (U).ι (p m) := by
  apply IsOpenImmersion.isPullback
  · exact (completeIdentityStageTorus_inclusion K n h i m).symm
  · rw [Scheme.Opens.opensRange_ι]
    exact completePointIdentityOpen_stage_preimage K n h i m

/-- The full Laurent scheme is the identity parameter's actual original adic base change. -/
theorem completeIdentityStageTorus_base_isPullback (m : ℕ) :
    IsPullback (completeIdentityStageTorus K n h i m)
      (Spec.map (CommRingCat.ofHom (algebraMap (Ring K m) (Ring K m)[T;T⁻¹])))
      ((U).ι ≫ exactVeroneseProjToBase K n h) (baseToSeries K m) := by
  have hp := (completeIdentityStageTorus_isPullback K n h i m).paste_vert
    (originalStageToCompatibleProj_isPullback K n h m)
  simpa only [family, PolygonInfinitesimal.family, Over.mk_hom, edge_toBase] using hp

/-- Coordinate one is exactly the original identity marking over the unchanged finite base. -/
@[reassoc] theorem completeIdentityStageTorus_one (m : ℕ) :
    PolygonSmoothing.markedTorusSection (1 : (Ring K m)ˣ) ≫
        completeIdentityStageTorus K n h i m =
      baseToSeries K m ≫ completePointIdentityMarking K n h i := by
  apply (cancel_mono (U).ι).mp
  rw [Category.assoc, completeIdentityStageTorus_inclusion,
    Category.assoc, completePointIdentityMarking_inclusion]
  rw [edge, ← Category.assoc, PolygonSmoothing.markedTorusSection_left_assoc]
  exact (baseToSeries_completeBaseMarking K n h i m).symm

end FLT.Mazur.PolygonInfinitesimalStages

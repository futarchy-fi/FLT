/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointIdentityAffine

/-!
# Original marking maps on the finite affine identity charts

Both closed markings retain the original complete base. Their full ideals
are the restrictions of the original source and target marking ideals.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S₀" => Spec (CommRingCat.of (PowerSeries K))
local notation "W" => completePointWeierstrassCurve K n h i
local notation "V" => completePointOriginOpen K n h i
local notation "q" => completePointToOrigin K n h i
local notation "s" => completePointMarkingOrigin K n h i
local notation "U" => completePointIdentityAffineOpen K n h i
local notation "A" => (q) ⁻¹ᵁ (U)

/-- The original marking lifted to the actual finite affine source. -/
def completePointIdentityAffineSourceMarking : S₀ ⟶ (A).toScheme :=
  IsOpenImmersion.lift (A).ι (s) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact (completePointIdentityAffineOpen_spec K n h i).1 ⟨t, rfl⟩)

/-- The source lift preserves the original marking morphism. -/
@[reassoc] theorem completePointIdentityAffineSourceMarking_inclusion :
    completePointIdentityAffineSourceMarking K n h i ≫ (A).ι = (s) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The original marking on the actual finite affine target. -/
def completePointIdentityAffineTargetMarking : S₀ ⟶ (U).toScheme :=
  completePointIdentityAffineSourceMarking K n h i ≫ ((q) ∣_ (U))

/-- The target marking retains the original cubic-origin morphism. -/
@[reassoc] theorem completePointIdentityAffineTargetMarking_inclusion :
    completePointIdentityAffineTargetMarking K n h i ≫ (U).ι =
      (S₀).toSpecΓ ≫ originNeighborhoodSection (W) := by
  rw [completePointIdentityAffineTargetMarking, Category.assoc, morphismRestrict_ι,
    completePointIdentityAffineSourceMarking_inclusion_assoc,
    completePointMarkingOrigin_toOrigin]

/-- The actual target marking is a closed immersion. -/
theorem completePointIdentityAffineTargetMarking_closed :
    IsClosedImmersion (completePointIdentityAffineTargetMarking K n h i) := by
  have : IsClosedImmersion (completePointIdentityAffineTargetMarking K n h i ≫ (U).ι) := by
    rw [completePointIdentityAffineTargetMarking_inclusion]
    infer_instance
  exact IsClosedImmersion.of_comp _ (U).ι

/-- The actual source marking is a closed immersion as well. -/
theorem completePointIdentityAffineSourceMarking_closed :
    IsClosedImmersion (completePointIdentityAffineSourceMarking K n h i) := by
  let _ := (completePointIdentityAffineOpen_spec K n h i).2.2.1
  have : IsClosedImmersion
      (completePointIdentityAffineSourceMarking K n h i ≫ ((q) ∣_ (U))) :=
    completePointIdentityAffineTargetMarking_closed K n h i
  exact IsClosedImmersion.of_comp _ ((q) ∣_ (U))

/-- The full target marking ideal is the restricted original cubic-origin ideal. -/
theorem completePointIdentityAffineTargetMarking_ker :
    (completePointIdentityAffineTargetMarking K n h i).ker =
      (originNeighborhoodSection (W)).ker.comap (U).ι := by
  have : IsClosedImmersion (completePointIdentityAffineTargetMarking K n h i ≫ (U).ι) := by
    rw [completePointIdentityAffineTargetMarking_inclusion]
    infer_instance
  rw [← ProjectiveLineMarkedCharts.ker_comap_mono
    (completePointIdentityAffineTargetMarking K n h i) (U).ι,
    completePointIdentityAffineTargetMarking_inclusion, Scheme.Hom.ker_comp_of_isIso]

/-- The full source marking ideal is the restricted original marking ideal. -/
theorem completePointIdentityAffineSourceMarking_ker :
    (completePointIdentityAffineSourceMarking K n h i).ker = (s).ker.comap (A).ι := by
  have : IsClosedImmersion (s) := by
    let _ := exactVeroneseProjToBase_isProper K n h
    have : IsClosedImmersion ((s) ≫ (V).ι) := by
      rw [completePointMarkingOrigin_inclusion]
      exact isClosedImmersion_section _ _ (completeBaseMarking_toBase K n h i)
    exact IsClosedImmersion.of_comp _ (V).ι
  have : IsClosedImmersion (completePointIdentityAffineSourceMarking K n h i ≫ (A).ι) := by
    rw [completePointIdentityAffineSourceMarking_inclusion]
    infer_instance
  rw [← completePointIdentityAffineSourceMarking_inclusion]
  exact (ProjectiveLineMarkedCharts.ker_comap_mono _ _).symm

/-- The original finite affine comparison pulls back the full target marking ideal. -/
theorem completePointIdentityAffine_marking_ideal :
    (completePointIdentityAffineTargetMarking K n h i).ker.comap ((q) ∣_ (U)) =
      (completePointIdentityAffineSourceMarking K n h i).ker := by
  rw [completePointIdentityAffineTargetMarking_ker,
    ← Scheme.IdealSheafData.comap_comp, morphismRestrict_ι,
    Scheme.IdealSheafData.comap_comp, ← completePointPulledOriginIdeal_neighborhood,
    completePointPulledOriginIdeal_eq_marking, completePointMarkingIdeal_neighborhood,
    completePointIdentityAffineSourceMarking_ker]

end FLT.Mazur.PolygonInfinitesimalStages

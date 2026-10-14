/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointIdentityFinite
public import FLT.Mazur.PolygonCompletePointOriginParameterRegular
public import FLT.Mazur.FiniteAffineBaseNeighborhood

/-!
# Actual affine finite charts around the entire original identity

The complete base is local. An affine open containing the image of its
closed point therefore contains the whole identity. Shrinking the proper
finite neighborhood gives affine source and target with the original map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S₀" => Spec (CommRingCat.of (PowerSeries K))
local notation "W" => completePointWeierstrassCurve K n h i
local notation "V" => completePointOriginOpen K n h i
local notation "q" => completePointToOrigin K n h i
local notation "s" => completePointMarkingOrigin K n h i

/-- The actual parameter-neighborhood marking square is a Cartesian identity. -/
theorem completePointOriginIdentity_isPullback :
    IsPullback (𝟙 S₀) (s) ((s) ≫ (q)) (q) := by
  apply (completePointToOrigin_marking_isPullback K n h i).flip.of_iso
    (Iso.refl _) (asIso (S₀).toSpecΓ).symm (Iso.refl _) (Iso.refl _)
  · simp
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv,
      completePointMarkingOrigin_toOrigin, IsIso.inv_hom_id_assoc]
  · simp

/-- Both original schemes admit affine finite charts containing the whole marking. -/
theorem completePointOriginIdentity_exists_affine_finite :
    ∃ U : (Spec (.of (OriginNeighborhood (W)))).Opens,
      Set.range ((s) ≫ (q)) ⊆ U ∧ IsAffineOpen U ∧
        IsFinite ((q) ∣_ U) ∧ IsAffineOpen ((q) ⁻¹ᵁ U) := by
  let _ := completePointToOrigin_proper K n h i
  obtain ⟨B, hB, hfin⟩ := CartesianIdentity.exists_finite_identity_neighborhood (s) (q)
    (completePointOriginIdentity_isPullback K n h i)
  have hb : ((s) ≫ (q)) (IsLocalRing.closedPoint (PowerSeries K)) ∈ B :=
    hB ⟨_, rfl⟩
  obtain ⟨U, hU, htU, hUB⟩ := exists_isAffineOpen_mem_and_subset hb
  let _ := Approximation.finite_morphismRestrict_of_le (q) hUB
  let _ : IsAffine U.toScheme := hU
  refine ⟨U, ?_, hU, inferInstance, isAffine_of_isAffineHom ((q) ∣_ U)⟩
  rintro _ ⟨t, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint t).map ((s) ≫ (q)).continuous).mem_open
    U.isOpen htU

/-- Retain a chosen actual affine target containing the entire original identity. -/
def completePointIdentityAffineOpen : (Spec (.of (OriginNeighborhood (W)))).Opens :=
  (completePointOriginIdentity_exists_affine_finite K n h i).choose

/-- The chosen chart retains all four proved properties of the original comparison. -/
theorem completePointIdentityAffineOpen_spec :
    Set.range ((s) ≫ (q)) ⊆ completePointIdentityAffineOpen K n h i ∧
      IsAffineOpen (completePointIdentityAffineOpen K n h i) ∧
      IsFinite ((q) ∣_ completePointIdentityAffineOpen K n h i) ∧
      IsAffineOpen ((q) ⁻¹ᵁ completePointIdentityAffineOpen K n h i) :=
  (completePointOriginIdentity_exists_affine_finite K n h i).choose_spec

/-- The actual parameter on the finite affine source is still regular. -/
theorem completePointIdentityAffine_parameter_regular :
    IsRegular ((((q) ⁻¹ᵁ completePointIdentityAffineOpen K n h i).ι ≫ (q)).appTop
      (originParameterSection (W))) :=
  completePointToOrigin_parameter_regular_on K n h i _

end FLT.Mazur.PolygonInfinitesimalStages

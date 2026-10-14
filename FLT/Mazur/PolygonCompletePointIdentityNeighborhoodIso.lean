/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointIdentityPrincipal
public import FLT.Mazur.AffinePrincipalComparisonIso

/-!
# An actual identity neighborhood isomorphism for the complete polygon map

The original finite identity chart restricts to an isomorphism on one
principal target neighborhood containing the entire unchanged marking.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart FiniteCartierComparison
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointIdentityAffineOpen completePointToOrigin completePointOriginOpen
  completePointIdentityAffineSourceMarking completePointIdentityAffineTargetMarking
  completePointWeierstrassCurve

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S₀" => Spec (CommRingCat.of (PowerSeries K))
local notation "q" => completePointToOrigin K n h i
local notation "U" => completePointIdentityAffineOpen K n h i
local notation "f" => completePointIdentityAffineMap K n h i
local notation "mT" => completePointIdentityAffineTargetMarking K n h i

/-- The original comparison is an isomorphism over a principal open containing the full marking. -/
theorem completePointIdentityAffine_exists_marking_principal_isIso :
    ∃ r : Γ((U).toScheme, ⊤),
      Set.range (mT) ⊆ (U).toScheme.basicOpen r ∧
      IsIso ((f) ∣_ (U).toScheme.basicOpen r) := by
  let _ : IsAffine (U).toScheme := (completePointIdentityAffineOpen_spec K n h i).2.1
  let _ : IsAffine (((q) ⁻¹ᵁ (U)).toScheme) :=
    (completePointIdentityAffineOpen_spec K n h i).2.2.2
  let _ := (f).appTop.hom.toAlgebra
  let H := completePointIdentityAffine_exists_principal_bijective K n h i
  let r := H.choose
  have hr := H.choose_spec
  refine ⟨r, ?_, affine_principal_isIso (f) r hr.2⟩
  rintro _ ⟨x, rfl⟩
  rw [← Scheme.toSpecΓ_preimage_basicOpen]
  exact completePointIdentityAffine_marking_mem_principal K n h i r hr.1 x

/-- An actual open neighborhood of the identity, with the original restricted morphism. -/
def completePointIdentityIsoOpen : (U).toScheme.Opens :=
  (U).toScheme.basicOpen
    (completePointIdentityAffine_exists_marking_principal_isIso K n h i).choose

/-- The chosen actual open keeps the full original marking and the proved isomorphism. -/
theorem completePointIdentityIsoOpen_spec :
    Set.range (mT) ⊆ completePointIdentityIsoOpen K n h i ∧
      IsIso ((f) ∣_ completePointIdentityIsoOpen K n h i) :=
  (completePointIdentityAffine_exists_marking_principal_isIso K n h i).choose_spec

local notation "B" => completePointIdentityIsoOpen K n h i

/-- The actual neighborhood isomorphism, whose forward map is the original restriction. -/
def completePointIdentityNeighborhoodIso :
    ((f) ⁻¹ᵁ (B)).toScheme ≅ (B).toScheme := by
  let _ : IsIso ((f) ∣_ (B)) := (completePointIdentityIsoOpen_spec K n h i).2
  exact asIso ((f) ∣_ (B))

/-- The constructed isomorphism retains the original forward morphism exactly. -/
theorem completePointIdentityNeighborhoodIso_hom :
    (completePointIdentityNeighborhoodIso K n h i).hom = (f) ∣_ (B) := rfl

/-- The comparison commutes with the original affine chart inclusions. -/
@[reassoc] theorem completePointIdentityNeighborhoodIso_inclusion :
    (completePointIdentityNeighborhoodIso K n h i).hom ≫ (B).ι =
      ((f) ⁻¹ᵁ (B)).ι ≫ (f) :=
  morphismRestrict_ι (f) (B)

/-- The inverse is an inverse over the original finite affine target chart. -/
@[reassoc] theorem completePointIdentityNeighborhoodIso_inv_inclusion :
    (completePointIdentityNeighborhoodIso K n h i).inv ≫ ((f) ⁻¹ᵁ (B)).ι ≫ (f) =
      (B).ι := by
  rw [← completePointIdentityNeighborhoodIso_inclusion, Iso.inv_hom_id_assoc]

end FLT.Mazur.PolygonInfinitesimalStages

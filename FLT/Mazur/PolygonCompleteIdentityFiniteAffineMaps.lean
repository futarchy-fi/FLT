/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFiniteAffineNeighborhood

/-!
# Compatible finite maps into a fixed original affine target

Restrict the original finite action inputs to actual original input opens.
The full finite scaling factors through the chosen fixed affine target and
commutes with every adjacent restriction as a scheme morphism.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "P" => completeIdentityActionProduct K n h 0
local notation "X" => exactVeroneseProj K n h
local notation "j" m => completeIdentityFiniteInput K n h 0 m
local notation "f" m => completeIdentityFiniteScaling K n h m
variable (U : (completeIdentityActionProduct K n h 0).Opens)
  (V : (exactVeroneseProj K n h).Opens)
  (hUV : completeIdentityFiniteInput K n h 0 0 ⁻¹ᵁ U ≤
    completeIdentityFiniteScaling K n h 0 ⁻¹ᵁ V)

/-- The literal original finite input restricted to the chosen original open. -/
abbrev completeIdentityFiniteAffineDomain (m : ℕ) : Scheme := pullback (j m) U.ι

include hUV in
/-- The whole restricted finite scaling has image inside the fixed original target. -/
theorem completeIdentityFiniteAffine_range (m : ℕ) :
    Set.range (pullback.fst (j m) U.ι ≫ (f m)) ⊆ Set.range V.ι := by
  rintro _ ⟨x, rfl⟩
  have hx : (j m) (pullback.fst (j m) U.ι x) ∈ U := by
    have he : pullback.fst (j m) U.ι ≫ (j m) = pullback.snd (j m) U.ι ≫ U.ι :=
      pullback.condition
    have he := congrArg (fun k ↦ k x) he
    change (j m) (pullback.fst (j m) U.ι x) = U.ι (pullback.snd (j m) U.ι x) at he
    rw [he]
    exact (pullback.snd (j m) U.ι x).property
  exact ⟨⟨_, completeIdentityFiniteAffine_all K n h U V hUV m hx⟩, rfl⟩

/-- The actual finite action with values in one unchanged original target affine. -/
def completeIdentityFiniteAffineMap (m : ℕ) :
    completeIdentityFiniteAffineDomain K n h U m ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι (pullback.fst (j m) U.ι ≫ (f m))
    (completeIdentityFiniteAffine_range K n h U V hUV m)

/-- The affine target factorization preserves the entire original finite action. -/
@[reassoc] theorem completeIdentityFiniteAffineMap_inclusion (m : ℕ) :
    completeIdentityFiniteAffineMap K n h U V hUV m ≫ V.ι =
      pullback.fst (j m) U.ι ≫ (f m) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The adjacent finite restriction retains the exact original source open. -/
def completeIdentityFiniteAffineRestriction (m : ℕ) :
    completeIdentityFiniteAffineDomain K n h U m ⟶
      completeIdentityFiniteAffineDomain K n h U (m + 1) :=
  pullback.map (j m) U.ι (j (m + 1)) U.ι
    (completeIdentityFiniteRestriction K n h m) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, completeIdentityFiniteRestriction_input]) (by simp)

/-- The actual adjacent affine-target maps agree, including all original nilpotents. -/
@[reassoc] theorem completeIdentityFiniteAffineMap_restriction (m : ℕ) :
    completeIdentityFiniteAffineRestriction K n h U m ≫
        completeIdentityFiniteAffineMap K n h U V hUV (m + 1) =
      completeIdentityFiniteAffineMap K n h U V hUV m := by
  apply (cancel_mono V.ι).mp
  rw [Category.assoc, completeIdentityFiniteAffineMap_inclusion,
    completeIdentityFiniteAffineMap_inclusion, completeIdentityFiniteAffineRestriction,
    pullback.map, pullback.lift_fst_assoc, Category.assoc,
    completeIdentityFiniteRestriction_scaling]

/-- The chosen affine-valued finite action retains the full original cubic equation. -/
@[reassoc] theorem completeIdentityFiniteAffineMap_cubic (m : ℕ) :
    completeIdentityFiniteAffineMap K n h U V hUV m ≫ V.ι ≫
        completePointToIntegralCubic K n h 0 =
      pullback.snd (j m) U.ι ≫ U.ι ≫ completeIdentityActionTarget K n h 0 := by
  rw [completeIdentityFiniteAffineMap_inclusion_assoc,
    completeIdentityFiniteComparison_all, ← Category.assoc, pullback.condition,
    Category.assoc]

end FLT.Mazur.PolygonInfinitesimalStages

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAffineQuotientStage
public import FLT.Mazur.AdicAffineMorphismLift

/-!
# Constructing the completed action on actual original affine neighborhoods

The chosen original affine neighborhoods supply compatible finite morphisms
into one fixed affine target. Their coordinates construct a genuine map from
the original source's parameter completion into the original polygon.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (U : (completeIdentityActionProduct K n h 0).affineOpens)
  (V : (exactVeroneseProj K n h).affineOpens)
  (hUV : completeIdentityFiniteInput K n h 0 0 ⁻¹ᵁ U.1 ≤
    completeIdentityFiniteScaling K n h 0 ⁻¹ᵁ V.1)

/-- The original affine input's coordinate ring, with no change of scalars. -/
abbrev completeIdentityAffineSourceRing : CommRingCat := Γ(U.1.toScheme, ⊤)

local notation "R" => completeIdentityAffineSourceRing K n h U

/-- The actual spectrum presentation of the original affine input open. -/
abbrev completeIdentityAffineSourceMap :
    Spec (R) ⟶ completeIdentityActionProduct K n h 0 :=
  U.1.toScheme.isoSpec.inv ≫ U.1.ι

local notation "v" => completeIdentityAffineSourceMap K n h U
local notation "I" => completeIdentityAffineIdeal K n h (A := (R)) (v)
local notation "j" m => completeIdentityAffineQuotientToFinite K n h (v) m
local notation "f" m => completeIdentityFiniteScaling K n h m
local notation "q" m => Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((I) ^ (m + 1))))

include hUV in
/-- All actual parameter quotients land in the same original target affine. -/
theorem completeIdentityAffineFinite_range (m : ℕ) :
    Set.range ((j m) ≫ (f m)) ⊆ Set.range V.1.ι := by
  rintro _ ⟨x, rfl⟩
  have hx : completeIdentityFiniteInput K n h 0 m ((j m) x) ∈ U.1 := by
    have he := congrArg (fun k ↦ k x)
      (completeIdentityAffineQuotientToFinite_input K n h (v) m)
    change completeIdentityFiniteInput K n h 0 m ((j m) x) = (v) ((q m) x) at he
    rw [he]
    exact (U.1.toScheme.isoSpec.inv ((q m) x)).property
  exact ⟨⟨_, completeIdentityFiniteAffine_all K n h U.1 V.1 hUV m hx⟩, rfl⟩

/-- The actual original finite action with its fixed affine target. -/
def completeIdentityAffineFiniteMap (m : ℕ) :
    Spec (.of ((R) ⧸ (I) ^ (m + 1))) ⟶ V.1.toScheme :=
  IsOpenImmersion.lift V.1.ι ((j m) ≫ (f m))
    (completeIdentityAffineFinite_range K n h U V hUV m)

/-- The factorization preserves the entire original finite scaling. -/
@[reassoc] theorem completeIdentityAffineFiniteMap_inclusion (m : ℕ) :
    completeIdentityAffineFiniteMap K n h U V hUV m ≫ V.1.ι = (j m) ≫ (f m) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The actual affine-valued finite morphisms agree at adjacent orders. -/
@[reassoc] theorem completeIdentityAffineFiniteMap_restriction (m : ℕ) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (S := (I) ^ (m + 2)) (T := (I) ^ (m + 1))
      (Ideal.pow_le_pow_right (Nat.le_succ (m + 1))))) ≫
        completeIdentityAffineFiniteMap K n h U V hUV (m + 1) =
      completeIdentityAffineFiniteMap K n h U V hUV m := by
  apply (cancel_mono V.1.ι).mp
  rw [Category.assoc, completeIdentityAffineFiniteMap_inclusion,
    completeIdentityAffineFiniteMap_inclusion,
    completeIdentityAffineQuotientToFinite_restriction_assoc,
    completeIdentityFiniteRestriction_scaling]

/-- The compatible actual finite actions construct the original completed polygon-valued map. -/
def completeIdentityAffineCompletionLift :
    Spec (.of (AdicCompletion (I) (R))) ⟶ exactVeroneseProj K n h :=
  AdicAffineMorphismLift.lift (I) V.1.toScheme
    (completeIdentityAffineFiniteMap K n h U V hUV)
    (completeIdentityAffineFiniteMap_restriction K n h U V hUV) ≫ V.1.ι

/-- Every positive stage recovers the whole original finite action, including its node inputs. -/
@[reassoc] theorem completeIdentityAffineCompletionLift_evaluation (m : ℕ) :
    Spec.map (CommRingCat.ofHom (AdicCompletion.evalₐ (I) (m + 1)).toRingHom) ≫
        completeIdentityAffineCompletionLift K n h U V hUV = (j m) ≫ (f m) := by
  rw [completeIdentityAffineCompletionLift, AdicAffineMorphismLift.evaluation_lift_assoc,
    completeIdentityAffineFiniteMap_inclusion]

end FLT.Mazur.PolygonInfinitesimalStages

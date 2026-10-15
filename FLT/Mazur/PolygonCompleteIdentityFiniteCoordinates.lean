/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFinitePair

/-!
# Actual Laurent coordinates of original finite multiplication

The original multiplication lifts through the proved base-change square.
This constructs its Laurent-valued coordinate map with all nilpotents retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "A" => Ring K m
local notation "G" => completePointOriginalBaseGroup K n h i
local notation "e" => completeIdentityStageTorus K n h i m
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap (A) (A)[T;T⁻¹]))
local notation "p" => Spec.map (CommRingCat.ofHom
  (algebraMap (A)[T;T⁻¹] (A)[T;T⁻¹][T;T⁻¹]))

/-- Original multiplication is over the unchanged finite coefficient base. -/
@[reassoc] theorem completeIdentityFiniteOriginalMul_base :
    completeIdentityFiniteOriginalMul K n h i m ≫ (G).X.hom =
      (p) ≫ (b) ≫ baseToSeries K m := by
  have hm := (μ[(G).X]).w
  change (μ[(G).X]).left ≫ (G).X.hom =
    pullback.fst (G).X.hom (G).X.hom ≫ (G).X.hom at hm
  rw [completeIdentityFiniteOriginalMul, Category.assoc, hm,
    completeIdentityFinitePair_fst_assoc,
    (completeIdentityFiniteParameter_isPullback K n h i m).w]

/-- The actual original law expressed in the full finite Laurent chart. -/
def completeIdentityFiniteMulCoordinates :
    PolygonSmoothing.branchTorus (A)[T;T⁻¹] ⟶ PolygonSmoothing.branchTorus (A) :=
  (completeIdentityFiniteParameter_isPullback K n h i m).lift
    (completeIdentityFiniteOriginalMul K n h i m) ((p) ≫ (b))
    (by simpa only [Category.assoc] using completeIdentityFiniteOriginalMul_base K n h i m)

/-- These coordinates recover the actual original multiplication, not a substitute law. -/
@[reassoc] theorem completeIdentityFiniteMulCoordinates_original :
    completeIdentityFiniteMulCoordinates K n h i m ≫ (e) =
      completeIdentityFiniteOriginalMul K n h i m := IsPullback.lift_fst _ _ _ _

/-- The coordinate map is a morphism over the entire finite coefficient ring. -/
@[reassoc] theorem completeIdentityFiniteMulCoordinates_base :
    completeIdentityFiniteMulCoordinates K n h i m ≫ (b) = (p) ≫ (b) :=
  IsPullback.lift_snd _ _ _ _

/-- Original multiplication and the unchanged base uniquely determine these coordinates. -/
theorem completeIdentityFiniteMulCoordinates_unique
    (f : PolygonSmoothing.branchTorus (A)[T;T⁻¹] ⟶ PolygonSmoothing.branchTorus (A))
    (hf : f ≫ (e) = completeIdentityFiniteOriginalMul K n h i m)
    (hb : f ≫ (b) = (p) ≫ (b)) : f = completeIdentityFiniteMulCoordinates K n h i m := by
  apply (completeIdentityFiniteParameter_isPullback K n h i m).hom_ext
  · rw [hf, completeIdentityFiniteMulCoordinates_original]
  · rw [hb, completeIdentityFiniteMulCoordinates_base]

end FLT.Mazur.PolygonInfinitesimalStages

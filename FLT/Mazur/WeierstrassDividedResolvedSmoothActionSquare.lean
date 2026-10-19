/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResolvedSmoothAction
public import FLT.Mazur.WeierstrassDividedGlobalActionSmooth

/-!
# The resolved smooth action is a Cartesian restriction

The entire smooth second-input product is also the inverse image of the
smooth output. Thus the restricted action inherits smoothness and surjectivity
by base change, with all original projections retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "s" => integralSmoothStructure W
local notation "t" => (U).ι ≫ base

/-- Include the entire smooth-input product in the original whole-model action product. -/
def finiteGlobalSmoothActionInput : pullback s t ⟶ finiteGlobalActionProduct hπ data j hj :=
  pullback.lift (pullback.fst s t) (pullback.snd s t ≫ (U).ι)
    (by rw [Category.assoc]; exact pullback.condition)

/-- The first parameter is the unchanged original smooth point. -/
@[reassoc] theorem finiteGlobalSmoothActionInput_fst :
    finiteGlobalSmoothActionInput hπ data j hj ≫ pullback.fst s base = pullback.fst s t :=
  pullback.lift_fst _ _ _

/-- The second parameter is the full resolved smooth-open inclusion. -/
@[reassoc] theorem finiteGlobalSmoothActionInput_snd :
    finiteGlobalSmoothActionInput hπ data j hj ≫ pullback.snd s base =
      pullback.snd s t ≫ (U).ι := pullback.lift_snd _ _ _

/-- The input square is the actual base change of the smooth-open inclusion. -/
theorem finiteGlobalSmoothActionInput_isPullback :
    IsPullback (pullback.snd s t) (finiteGlobalSmoothActionInput hπ data j hj)
      (U).ι (pullback.snd s base) := by
  apply (IsPullback.paste_vert_iff (IsPullback.of_hasPullback s base).flip
    (finiteGlobalSmoothActionInput_snd hπ data j hj).symm).mp
  simpa only [finiteGlobalSmoothActionInput_fst] using (IsPullback.of_hasPullback s t).flip

instance finiteGlobalSmoothActionInput_open :
    IsOpenImmersion (finiteGlobalSmoothActionInput hπ data j hj) :=
  MorphismProperty.of_isPullback (finiteGlobalSmoothActionInput_isPullback hπ data j hj)
    (inferInstanceAs (IsOpenImmersion (U).ι))

/-- The restricted action retains the exact whole-model action map. -/
@[reassoc] theorem finiteGlobalSmoothAction_inclusion :
    finiteGlobalSmoothAction hπ data j hj ≫ (U).ι =
      finiteGlobalSmoothActionInput hπ data j hj ≫ finiteGlobalAction hπ data j hj :=
  finiteGlobalSmoothPointAction_inclusion hπ data j hj _ _ _

/-- Smooth output is equivalent to smooth second input on the whole action product. -/
theorem finiteGlobalSmoothAction_isPullback :
    IsPullback (finiteGlobalSmoothAction hπ data j hj)
      (finiteGlobalSmoothActionInput hπ data j hj) (U).ι
      (finiteGlobalAction hπ data j hj) := by
  apply IsOpenImmersion.isPullback _ _ _ _
    (finiteGlobalSmoothAction_inclusion hπ data j hj).symm
  rw [Scheme.Opens.opensRange_ι, finiteGlobalAction_preimage_smooth]
  have he := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (finiteGlobalSmoothActionInput_isPullback hπ data j hj) ⊤
  simpa using he.symm

/-- The full resolved smooth action is a smooth morphism. -/
instance finiteGlobalSmoothAction_smooth : Smooth (finiteGlobalSmoothAction hπ data j hj) :=
  MorphismProperty.of_isPullback (finiteGlobalSmoothAction_isPullback hπ data j hj).flip
    (inferInstanceAs (Smooth (finiteGlobalAction hπ data j hj)))

/-- Every resolved smooth point is reached by the restricted action. -/
instance finiteGlobalSmoothAction_surjective :
    Surjective (finiteGlobalSmoothAction hπ data j hj) :=
  MorphismProperty.of_isPullback (finiteGlobalSmoothAction_isPullback hπ data j hj).flip
    (inferInstanceAs (Surjective (finiteGlobalAction hπ data j hj)))

end FLT.Mazur.WeierstrassDividedDepth

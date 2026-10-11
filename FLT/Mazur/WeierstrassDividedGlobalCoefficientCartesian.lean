/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalCoefficientAction

/-!
# The whole coefficient action is Cartesian

The actual smooth coefficient comparison identifies the extended action
domain with the base change of the original domain. The action itself is
therefore an actual base change, with no flatness assumption on coefficients.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n) (S : Type u) [CommRing S] [Algebra R S]
local notation "V" => W.map (algebraMap R S)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "fst" => pullback.fst q base
local notation "snd" => pullback.snd q base
local notation "f" => integralSmoothStructure W
local notation "fS" => integralSmoothStructure V

/-- Forget coefficients on both inputs of the whole action. -/
def finiteGlobalCoefficientActionProduct :
    pullback fS fst ⟶ finiteGlobalActionProduct hπ data j hj :=
  pullback.lift (pullback.fst fS fst ≫ originalSmoothCoefficientMap S W)
    (pullback.snd fS fst ≫ snd)
    (finiteGlobalCoefficientInput_condition hπ data j hj S _ _ pullback.condition)

/-- The coefficient domain map preserves the smooth parameter. -/
@[reassoc] theorem finiteGlobalCoefficientActionProduct_fst :
    finiteGlobalCoefficientActionProduct hπ data j hj S ≫ pullback.fst f base =
      pullback.fst fS fst ≫ originalSmoothCoefficientMap S W := pullback.lift_fst _ _ _

/-- The coefficient domain map preserves the model input. -/
@[reassoc] theorem finiteGlobalCoefficientActionProduct_snd :
    finiteGlobalCoefficientActionProduct hπ data j hj S ≫ pullback.snd f base =
      pullback.snd fS fst ≫ snd := pullback.lift_snd _ _ _

/-- The coefficient action retains exactly the original whole action morphism. -/
@[reassoc] theorem finiteGlobalCoefficientAction_projection :
    finiteGlobalCoefficientAction hπ data j hj S ≫ snd =
      finiteGlobalCoefficientActionProduct hπ data j hj S ≫ finiteGlobalAction hπ data j hj :=
  finiteGlobalCoefficientPointAction_projection hπ data j hj S _ _ _

/-- The actual coefficient action domain is Cartesian over its model input. -/
theorem finiteGlobalCoefficientActionProduct_isPullback :
    IsPullback (finiteGlobalCoefficientActionProduct hπ data j hj S)
      (pullback.snd fS fst) (pullback.snd f base) snd := by
  let H := originalSmoothCoefficientMap_isPullback S W
  have compat (s : PullbackCone (pullback.snd f base) snd) :
      (s.fst ≫ pullback.fst f base) ≫ f = (s.snd ≫ fst) ≫ q := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, s.condition,
      Category.assoc, ← pullback.condition, Category.assoc]
  let lift (s : PullbackCone (pullback.snd f base) snd) : s.pt ⟶ pullback fS fst :=
    pullback.lift (H.lift (s.fst ≫ pullback.fst f base) (s.snd ≫ fst) (compat s)) s.snd
      (H.lift_snd _ _ _)
  have hl (s : PullbackCone (pullback.snd f base) snd) :
      lift s ≫ finiteGlobalCoefficientActionProduct hπ data j hj S = s.fst := by
    dsimp only [lift]
    apply pullback.hom_ext
    · rw [Category.assoc, finiteGlobalCoefficientActionProduct_fst,
        ← Category.assoc, pullback.lift_fst, H.lift_fst]
    · rw [Category.assoc, finiteGlobalCoefficientActionProduct_snd,
        ← Category.assoc, pullback.lift_snd]
      exact s.condition.symm
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (finiteGlobalCoefficientActionProduct_snd hπ data j hj S) lift hl
    (fun _ => pullback.lift_snd _ _ _) ?_)
  intro s m hm hn
  dsimp only [lift]
  apply pullback.hom_ext
  · apply H.hom_ext
    · rw [Category.assoc, ← finiteGlobalCoefficientActionProduct_fst,
        ← Category.assoc, hm, pullback.lift_fst, H.lift_fst]
    · rw [Category.assoc, pullback.condition, ← Category.assoc, hn,
        pullback.lift_fst, H.lift_snd]
  · exact hn.trans (pullback.lift_snd _ _ _).symm

/-- The constructed coefficient action square is a genuine pullback. -/
theorem finiteGlobalCoefficientAction_isPullback :
    IsPullback (finiteGlobalCoefficientActionProduct hπ data j hj S)
      (finiteGlobalCoefficientAction hπ data j hj S) (finiteGlobalAction hπ data j hj) snd := by
  apply IsPullback.of_bot _ (finiteGlobalCoefficientAction_projection hπ data j hj S).symm
    (IsPullback.of_hasPullback q base).flip
  have H := (finiteGlobalCoefficientActionProduct_isPullback hπ data j hj S).paste_vert
    (IsPullback.of_hasPullback q base).flip
  simpa only [finiteGlobalCoefficientAction_structure, finiteGlobalAction_structure,
    pullback.condition] using H

end FLT.Mazur.WeierstrassDividedDepth

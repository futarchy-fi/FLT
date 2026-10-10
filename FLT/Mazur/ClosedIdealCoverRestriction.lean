/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Restricting compatible closed families on an open cover

Compatibility of actual ideal sheaves makes the restriction of one closed
family to a second base chart factor through that chart's closed family.
This constructs the morphisms needed for effective closed-family descent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace FLT.Mazur.ClosedIdealCover

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}

/-- An ideal sheaf vanishes on its own actual closed subscheme. -/
theorem comap_subschemeι_eq_bot (J : X.IdealSheafData) : J.comap J.subschemeι = ⊥ := by
  exact (pullback.fst J.subschemeι J.subschemeι).ker_eq_bot_of_isIso

variable (C : X.OpenCover) (J : ∀ i : C.I₀, (C.X i).IdealSheafData)
variable (hJ : ∀ i j, (J i).comap (pullback.fst (C.f i) (C.f j)) =
  (J j).comap (pullback.snd (C.f i) (C.f j)))

/-- The actual closed family in a cover chart maps to the original base. -/
def chartToBase (i : C.I₀) : (J i).subscheme ⟶ X := (J i).subschemeι ≫ C.f i

include hJ in
/-- Restricting a chart family to another base chart kills that chart's ideal. -/
theorem restriction_comap_eq_bot (i j : C.I₀) :
    (J j).comap (pullback.snd (chartToBase C J i) (C.f j)) = ⊥ := by
  let a := pullback.lift
    (pullback.fst (chartToBase C J i) (C.f j) ≫ (J i).subschemeι)
    (pullback.snd (chartToBase C J i) (C.f j))
    (by simpa only [Category.assoc, chartToBase] using
      (pullback.condition (f := chartToBase C J i) (g := C.f j)))
  have h := congrArg (fun K ↦ K.comap a) (hJ i j)
  rw [← comap_comp, ← comap_comp, pullback.lift_fst, pullback.lift_snd,
    comap_comp, comap_subschemeι_eq_bot, comap_bot] at h
  exact h.symm

/-- The actual map from a restricted closed family to the second chart family. -/
def restriction (i j : C.I₀) :
    pullback (chartToBase C J i) (C.f j) ⟶ (J j).subscheme :=
  IsClosedImmersion.lift (J j).subschemeι (pullback.snd _ _) (by
    rw [ker_subschemeι, ← map_bot (pullback.snd (chartToBase C J i) (C.f j)),
      le_map_iff_comap_le, restriction_comap_eq_bot C J hJ])

/-- The restricted family map recovers the original projection into the base chart. -/
@[reassoc]
theorem restriction_subschemeι (i j : C.I₀) :
    restriction C J hJ i j ≫ (J j).subschemeι =
      pullback.snd (chartToBase C J i) (C.f j) := IsClosedImmersion.lift_fac _ _ _

/-- The restricted family morphism respects the map to the original ambient scheme. -/
@[reassoc]
theorem restriction_toBase (i j : C.I₀) :
    restriction C J hJ i j ≫ chartToBase C J j =
      pullback.fst (chartToBase C J i) (C.f j) ≫ chartToBase C J i := by
  change restriction C J hJ i j ≫ (J j).subschemeι ≫ C.f j = _
  rw [← Category.assoc, restriction_subschemeι]
  exact pullback.condition.symm

/-- Restricting one family to a second chart computes the full family intersection. -/
theorem restriction_isPullback (i j : C.I₀) :
    IsPullback (pullback.fst (chartToBase C J i) (C.f j)) (restriction C J hJ i j)
      (chartToBase C J i) (chartToBase C J j) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (restriction_toBase C J hJ i j).symm
    (fun s ↦ pullback.lift s.fst (s.snd ≫ (J j).subschemeι)
      (by simpa only [Category.assoc, chartToBase] using s.condition)) ?_ ?_ ?_)
  · intro s
    exact pullback.lift_fst _ _ _
  · intro s
    rw [← cancel_mono (J j).subschemeι, Category.assoc,
      restriction_subschemeι, pullback.lift_snd]
  · intro s m hm _
    apply (cancel_mono (pullback.fst (chartToBase C J i) (C.f j))).mp
    exact hm.trans (pullback.lift_fst _ _ _).symm

include hJ in
/-- The full intersection of compatible chart families is open in the first family. -/
theorem intersection_fst_isOpenImmersion (i j : C.I₀) :
    IsOpenImmersion (pullback.fst (chartToBase C J i) (chartToBase C J j)) := by
  have h := restriction_isPullback C J hJ i j
  rw [← h.isoPullback_inv_fst]
  infer_instance

end FLT.Mazur.ClosedIdealCover

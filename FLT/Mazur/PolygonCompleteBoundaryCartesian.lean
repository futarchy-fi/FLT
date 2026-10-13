/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryTranslation
public import FLT.Mazur.PolygonCompleteClosedFiber

/-!
# The actual translated boundary is the complete family's closed base change

The maps recovering product lines are cartesian over the original complete
coefficient base. Their comparison with the actual complete-family fiber
preserves both projections and retains arbitrary varying translations.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonParameterTranslation PolygonUniversalAction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase translationIso
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of K))
  (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n))
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
local notation "τ" => translationIso K n hn p q hp g c

/-- The product-recovery inclusion is the original cartesian closed-fiber inclusion. -/
theorem completeBoundaryInclusion_eq_closed :
    completeBoundaryInclusion K n h = completeClosedFiberInclusion K n h := rfl

/-- Arbitrary parameter change retains the actual complete-family cartesian square. -/
theorem completeBoundaryParameter_isPullback :
    IsPullback (completeBoundaryParameterMap K n h g) ((Over.pullback g).obj C).hom
      (exactVeroneseProjToBase K n h) (g ≫ completeClosedBase K) :=
  (IsPullback.of_hasPullback (C).hom g).paste_horiz (completeClosedFiber_isPullback K n h)

/-- Inverse translation preserves the actual cartesian square over the same parameter scheme. -/
theorem completeMovedBoundary_isPullback :
    IsPullback (completeMovedBoundaryMap K n h g c) ((Over.pullback g).obj C).hom
      (exactVeroneseProjToBase K n h) (g ≫ completeClosedBase K) := by
  let e := (Over.forget T).mapIso (τ)
  have hs : IsPullback e.inv ((Over.pullback g).obj C).hom
      ((Over.pullback g).obj C).hom (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨by
      change (τ).inv.left ≫ _ = _ ≫ 𝟙 T
      rw [Over.w, Category.comp_id]⟩
  change IsPullback (τ).inv.left _ _ _ at hs
  change IsPullback ((τ).inv.left ≫ completeBoundaryParameterMap K n h g) _ _ _
  simpa only [Category.id_comp] using
    hs.paste_horiz (completeBoundaryParameter_isPullback K n h g)

/-- The actual complete-family fiber identifies with the whole translated boundary polygon. -/
irreducible_def completeMovedBoundaryFiberIso :
    ((Over.pullback g).obj C).left ≅
      pullback (exactVeroneseProjToBase K n h) (g ≫ completeClosedBase K) :=
  (completeMovedBoundary_isPullback K n h g c).isoPullback

/-- The comparison keeps the original recovery map into the complete smoothing. -/
@[reassoc] theorem completeMovedBoundaryFiberIso_fst :
    (completeMovedBoundaryFiberIso K n h g c).hom ≫ pullback.fst _ _ =
      completeMovedBoundaryMap K n h g c := by
  rw [completeMovedBoundaryFiberIso_def]
  exact IsPullback.isoPullback_hom_fst _

/-- The comparison keeps the original parameter projection on the whole polygon. -/
@[reassoc] theorem completeMovedBoundaryFiberIso_snd :
    (completeMovedBoundaryFiberIso K n h g c).hom ≫ pullback.snd _ _ =
      ((Over.pullback g).obj C).hom := by
  rw [completeMovedBoundaryFiberIso_def]
  exact IsPullback.isoPullback_hom_snd _

end FLT.Mazur.PolygonInfinitesimalStages

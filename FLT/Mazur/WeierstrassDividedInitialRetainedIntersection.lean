/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialPrecedingExterior
public import FLT.Mazur.WeierstrassDividedInitialRetainedBoundary
public import FLT.Mazur.WeierstrassDividedExteriorIntersections

/-!
# Exact intersections of the initial and first retained charts

The original exterior pushout is cartesian, and all later open retentions
preserve its entire intersection, including its original localization maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (h1 : 1 ≤ n) (r : ℕ) (hr : 1 + r ≤ n)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le h1))
local notation "E₀" => initialExterior d
local notation "tail" => finiteStageRetained hπ data 1 h1 r hr
local notation "ext" => Exterior.exteriorChart (finiteExterior hπ data E₀ (1 + r) hr)
local notation "i" => finiteInitialChart hπ data (1 + r) hr
local notation "l" => olderSuccessiveChart hπ data 0 h1 r hr

/-- Later retention preserves the whole initial/first-successive chart intersection. -/
theorem initialRetainedIntegral_isPullback :
    IsPullback (E₀).attach (previousToX hπ d e) i l := by
  rw [finiteInitialChart, finiteRetained_stage_factor hπ data 1 h1 r hr]
  change IsPullback (E₀).attach (previousToX hπ d e)
    (((𝟙 _ ≫ (E₀).retained hπ e) ≫ tail) ≫ ext)
    ((E₀).newX hπ e ≫ tail ≫ ext)
  have H := (E₀).retained_newX_isPullback hπ e
  have H' : IsPullback (E₀).attach (previousToX hπ d e)
      ((E₀).retained hπ e ≫ (tail ≫ ext))
      ((E₀).newX hπ e ≫ (tail ≫ ext)) := IsPullback.of_isLimit
    (PullbackCone.isLimitOfCompMono _ _ (tail ≫ ext) H.cone H.isLimit)
  simpa only [Category.id_comp, Category.assoc] using H'

/-- The complete retained intersection is the original divided boundary. -/
def initialRetainedIntegralPullbackIso : boundary d ≅ pullback i l :=
  (initialRetainedIntegral_isPullback hπ data h1 r hr).isoPullback

/-- The initial projection is the original exterior attachment. -/
@[reassoc] theorem initialRetainedIntegralPullbackIso_initial :
    (initialRetainedIntegralPullbackIso hπ data h1 r hr).hom ≫
      pullback.fst i l = (E₀).attach :=
  (initialRetainedIntegral_isPullback hπ data h1 r hr).isoPullback_hom_fst

/-- The successive projection is the original preceding-boundary map. -/
@[reassoc] theorem initialRetainedIntegralPullbackIso_successive :
    (initialRetainedIntegralPullbackIso hπ data h1 r hr).hom ≫
      pullback.snd i l = previousToX hπ d e :=
  (initialRetainedIntegral_isPullback hπ data h1 r hr).isoPullback_hom_snd

local notation "a" => WeierstrassModificationX.overlapEquiv W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "b" => previousBoundaryEquiv hπ d e
local notation "t" => WeierstrassModificationX.t W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "u" => WeierstrassSuccessiveX.coord W (π ^ start) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 2

/-- Both original localization projections present the exact integral intersection. -/
theorem initialRetainedLocalized_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (AlgEquiv.symm a).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away t))))
      (Spec.map (CommRingCat.ofHom (AlgEquiv.symm b).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away u)))) i l := by
  change IsPullback (E₀).attach
    (Spec.map (CommRingCat.ofHom (AlgEquiv.symm b).toRingHom) ≫
      WeierstrassSuccessiveX.horizontalOpenInclusion W (π ^ start) π
        (Data.b3 e) (Data.b4 e) (Data.b6 e)) i l
  erw [previousBoundary_inverse_inclusion hπ d e]
  exact initialRetainedIntegral_isPullback hπ data h1 r hr

end FLT.Mazur.WeierstrassDividedDepth

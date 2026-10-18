/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingMarkedFamily
public import FLT.Mazur.PolygonParameterTranslation

/-!
# The complete one-gon smoothing over arbitrary boundary parameters

The original pinched one-gon is the actual closed fiber of the explicit
power-series smoothing. Arbitrary parameter change and inverse translation
retain that Cartesian square on the whole original curve.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.OneGonSmoothing
open PolygonParameterTranslation PolygonUniversalAction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] translationIso
variable (K : Type) [Field K]
local notation "C" => OneGonNormalization.polygon K
local notation "p" => OneGonNormalization.normalizationOver K
local notation "q" => OneGonNormalization.nodes K
local notation "h" => OneGonGlobalPushout.isPushout K (by decide)
local notation "t" => (PowerSeries.X : PowerSeries K)
local notation "b" => Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))

/-- The original closed one-gon maps into the actual complete smoothing. -/
def boundaryClosedMap : (C).left ⟶ (family (t)).left :=
  (powerSeriesClosedFiberIso K).hom ≫ pullback.fst (family (t)).hom (b)

/-- The original complete one-gon square is Cartesian. -/
theorem boundaryClosed_isPullback :
    IsPullback (boundaryClosedMap K) (C).hom (family (t)).hom (b) := by
  apply IsPullback.of_iso_pullback _ (powerSeriesClosedFiberIso K) rfl
    (powerSeriesClosedFiberIso_snd K)
  constructor
  rw [Category.assoc, pullback.condition,
    ← Category.assoc, powerSeriesClosedFiberIso_snd]

variable {T : Scheme} (g : T ⟶ Spec (.of K))
  (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K 1))
local notation "τ" => translationIso K 1 (by decide) (p) (q) (h) g c

/-- The whole original one-gon over a boundary parameter maps to the complete family. -/
def boundaryParameterMap : ((Over.pullback g).obj C).left ⟶ (family (t)).left :=
  pullback.fst (C).hom g ≫ boundaryClosedMap K

/-- Arbitrary boundary parameter change retains the actual complete-family square. -/
theorem boundaryParameter_isPullback :
    IsPullback (boundaryParameterMap K g) ((Over.pullback g).obj C).hom
      (family (t)).hom (g ≫ (b)) :=
  (IsPullback.of_hasPullback (C).hom g).paste_horiz (boundaryClosed_isPullback K)

/-- Recover the complete smoothing through the inverse of an actual varying translation. -/
def boundaryMovedMap : ((Over.pullback g).obj C).left ⟶ (family (t)).left :=
  (τ).inv.left ≫ boundaryParameterMap K g

/-- Every varying one-gon translation retains the complete-family Cartesian square. -/
theorem boundaryMoved_isPullback :
    IsPullback (boundaryMovedMap K g c) ((Over.pullback g).obj C).hom
      (family (t)).hom (g ≫ (b)) := by
  let e := (Over.forget T).mapIso (τ)
  have hs : IsPullback e.inv ((Over.pullback g).obj C).hom
      ((Over.pullback g).obj C).hom (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨by
      change (τ).inv.left ≫ _ = _ ≫ 𝟙 T
      rw [Over.w, Category.comp_id]⟩
  change IsPullback (τ).inv.left _ _ _ at hs
  change IsPullback ((τ).inv.left ≫ boundaryParameterMap K g) _ _ _
  simpa only [Category.id_comp] using hs.paste_horiz (boundaryParameter_isPullback K g)

/-- The actual complete fiber is the whole original translated one-gon. -/
irreducible_def boundaryMovedFiberIso :
    ((Over.pullback g).obj C).left ≅ pullback (family (t)).hom (g ≫ (b)) :=
  (boundaryMoved_isPullback K g c).isoPullback

/-- The comparison retains the original curve projection to the complete smoothing. -/
@[reassoc] theorem boundaryMovedFiberIso_fst :
    (boundaryMovedFiberIso K g c).hom ≫ pullback.fst _ _ = boundaryMovedMap K g c := by
  rw [boundaryMovedFiberIso_def]
  exact IsPullback.isoPullback_hom_fst _

/-- The comparison retains the original parameter projection on the whole one-gon. -/
@[reassoc] theorem boundaryMovedFiberIso_snd :
    (boundaryMovedFiberIso K g c).hom ≫ pullback.snd _ _ =
      ((Over.pullback g).obj C).hom := by
  rw [boundaryMovedFiberIso_def]
  exact IsPullback.isoPullback_hom_snd _

end FLT.Mazur.OneGonSmoothing

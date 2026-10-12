/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonProjectiveNormalizedParameter

/-!
# Retain every polygon label through full normalized parameters

The actual normalized slice point remembers the original coefficient parameter
and every auxiliary/cyclic label through the actual normalization group map.
Projection on the original side recovers the original chosen polygon marking.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart UniversalWeierstrass AuxiliaryLevel PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "W" => completeCartesianPointWeierstrass K n h L
  (Spec.map (CommRingCat.ofHom a)) p q hs
local notation "G" => completeProjectiveGroup K n h L a ha p q hs

variable (h2 : (2 : L) ≠ 0)
local notation "hΔ" => completeProjectiveEquation_discriminant K n h L a ha p q hs
local notation "base" => originalCoefficientBase
local notation "unitTwo" => Iff.mpr isUnit_iff_ne_zero h2

local notation "aO" => cyclicSchemeAuxiliaryPoint n (𝟙 _)
local notation "aN" => auxiliarySchemeNormalizedPoint aO

/-- The original-side projection retains exactly the native polygon full marking. -/
theorem completeProjectiveNormalizedOriginal_projection
    (hn : Nat.Coprime 4 n) (i : Fin n) {T : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) (c : CyclicLabels n) :
    (completeProjectiveUniversalFullParameter K n h L a ha p q hs h2 hn i f).left ≫
      (cyclicSchemeOriginalMarking n (𝟙 _) c).left ≫
        pullback.fst universalGroup.hom (aO ≫ levelFour.hom) =
          (completeProjectiveFullMarking K n h L a ha p q hs i f c).left ≫
            (originalCoefficientGroupIso (W i) unitTwo (hΔ i)).inv.hom.hom.hom.left ≫
              pullback.fst (integralCurveStructure smoothEquation)
                (base (W i) unitTwo (hΔ i)) := by
  rw [cyclicNaturalOriginalMarking_projection]
  exact completeProjectiveUniversalFullParameter_value K n h L a ha p q hs h2 hn i f c

/-- Every normalized polygon label is the projection of its actual normalized full marking. -/
theorem completeProjectiveNormalizedFullParameter_value
    (hn : Nat.Coprime 4 n) (i : Fin n) {T : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) (c : CyclicLabels n) :
    completeProjectiveNormalizedFullParameter K n h L a ha p q hs h2 hn i f ≫
      cyclicNormalizedSliceInclusion n ≫
        (cyclicAuxiliaryInclusion n ≫ value universalGroup (CyclicLabels n) c).left =
          (completeProjectiveUniversalFullParameter K n h L a ha p q hs h2 hn i f).left ≫
            (cyclicSchemeNormalizedMarking n (𝟙 _) c).left ≫
              pullback.fst universalGroup.hom (aN ≫ levelFour.hom) :=
  cyclicNaturalNormalizedSlicePoint_value n _ c

/-- The actual group comparison recovers the original polygon parameter label by label. -/
theorem completeProjectiveNormalizedFullMarking_compare
    (hn : Nat.Coprime 4 n) (i : Fin n) {T : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) (c : CyclicLabels n) :
    (completeProjectiveUniversalFullParameter K n h L a ha p q hs h2 hn i f).left ≫
      (cyclicSchemeNormalizedMarking n (𝟙 _) c).left ≫
        (auxiliarySchemeNormalizationGroupIso aO).hom.hom.hom.hom.left =
          (completeProjectiveUniversalFullParameter K n h L a ha p q hs h2 hn i f).left ≫
            (cyclicSchemeOriginalMarking n (𝟙 _) c).left :=
  cyclicNaturalNormalizedMarking_compare n _ c

/-- The normalized full parameter keeps the actual normalized auxiliary coefficient map. -/
@[reassoc] theorem completeProjectiveNormalizedFullParameter_base
    (hn : Nat.Coprime 4 n) (i : Fin n) {T : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) :
    completeProjectiveNormalizedFullParameter K n h L a ha p q hs h2 hn i f ≫
      cyclicNormalizedSliceInclusion n ≫ (cyclicAuxiliaryScheme n).hom =
        auxiliarySchemeNormalizedPoint (cyclicSchemeAuxiliaryPoint n
          (completeProjectiveUniversalFullParameter K n h L a ha p q hs h2 hn i f).left) ≫
            levelFour.hom := by
  have he := congrArg (fun z ↦ z ≫ levelFour.hom)
    (cyclicNaturalNormalizedSlicePoint_forget n
      (completeProjectiveUniversalFullParameter K n h L a ha p q hs h2 hn i f).left)
  simp only [Category.assoc, (forgetCyclic n).w] at he
  exact he

end FLT.Mazur.PolygonInfinitesimalStages

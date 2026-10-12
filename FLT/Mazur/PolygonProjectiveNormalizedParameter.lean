/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonProjectiveUniversalParameter
public import FLT.Mazur.UniversalWeierstrassCyclicNormalizationMapLabels

/-!
# The retained polygon full family in the actual normalized slice

The original full universal parameter now lands in the actual normalized cyclic
slice. Both the original parameter and its normalized full family commute with
every test-scheme map and retain the original auxiliary normalization.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonObj
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

/-- The original global full parameter commutes with all maps of test schemes. -/
@[reassoc] theorem completeProjectiveUniversalFullParameter_natural
    (hn : Nat.Coprime 4 n) (i : Fin n) {T U : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) (k : U ⟶ T) :
    (Over.map (base (W i) unitTwo (hΔ i))).map k ≫
      completeProjectiveUniversalFullParameter K n h L a ha p q hs h2 hn i f =
        completeProjectiveUniversalFullParameter K n h L a ha p q hs h2 hn i (k ≫ f) := by
  unfold completeProjectiveUniversalFullParameter originalFaithfulParameter
  rw [originalGroupParameter_natural, completeProjectiveFullParameter_natural]

/-- The actual normalized full-slice parameter of the original marked polygon family. -/
def completeProjectiveNormalizedFullParameter (hn : Nat.Coprime 4 n) (i : Fin n)
    {T : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) :
    T.left ⟶ cyclicNormalizedSlice n :=
  cyclicNaturalNormalizedSlicePoint n
    (completeProjectiveUniversalFullParameter K n h L a ha p q hs h2 hn i f).left

/-- The normalized full family is natural for all original test-scheme maps. -/
@[reassoc] theorem completeProjectiveNormalizedFullParameter_natural
    (hn : Nat.Coprime 4 n) (i : Fin n) {T U : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) (k : U ⟶ T) :
    k.left ≫ completeProjectiveNormalizedFullParameter K n h L a ha p q hs h2 hn i f =
      completeProjectiveNormalizedFullParameter K n h L a ha p q hs h2 hn i (k ≫ f) := by
  have he := congrArg Over.Hom.left
    (completeProjectiveUniversalFullParameter_natural K n h L a ha p q hs h2 hn i f k)
  change k.left ≫ (_ ≫ _) = _ ≫ _
  rw [← Category.assoc]
  exact congrArg (fun z ↦ z ≫ cyclicNormalizationSliceMap n) he

/-- Forgetting the cyclic factor retains the original auxiliary normalization exactly. -/
@[reassoc] theorem completeProjectiveNormalizedFullParameter_auxiliary
    (hn : Nat.Coprime 4 n) (i : Fin n) {T : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) :
    completeProjectiveNormalizedFullParameter K n h L a ha p q hs h2 hn i f ≫
      cyclicNormalizedSliceAuxiliary n =
        auxiliarySchemeNormalizedSlicePoint (cyclicSchemeAuxiliaryPoint n
          (completeProjectiveUniversalFullParameter K n h L a ha p q hs h2 hn i f).left) :=
  cyclicNaturalNormalizedSlicePoint_auxiliary n _

/-- The native original auxiliary scheme maps into the actual normalized full slice. -/
def completeProjectiveNormalizedAuxiliaryMap (hn : Nat.Coprime 4 n) (i : Fin n) :
    (completeProjectiveAuxiliaryScheme K n h L a ha p q hs i).left ⟶ cyclicNormalizedSlice n :=
  completeProjectiveNormalizedFullParameter K n h L a ha p q hs h2 hn i (𝟙 _)

end FLT.Mazur.PolygonInfinitesimalStages

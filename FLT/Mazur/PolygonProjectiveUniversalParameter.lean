/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonProjectiveAuxiliaryParameter
public import FLT.Mazur.UniversalWeierstrassOriginalParameter

/-!
# The original polygon full marking in the actual universal family

The coefficients of the original constructed cubic and its proved faithful full
marking give an actual morphism to cyclicAuxiliaryScheme. Every marked value
retains the original section through the actual universal group comparison.
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

include ha in
/-- The discriminant of the original chosen projective equation is a unit. -/
theorem completeProjectiveEquation_discriminant (i : Fin n) : IsUnit (W i).Δ := by
  let _ := completeCartesianPointWeierstrass_isElliptic K n h L a ha p q hs i
  exact WeierstrassCurve.isUnit_Δ _

variable (h2 : (2 : L) ≠ 0)
local notation "hΔ" => completeProjectiveEquation_discriminant K n h L a ha p q hs
local notation "base" => originalCoefficientBase
local notation "unitTwo" => Iff.mpr isUnit_iff_ne_zero h2

/-- The original full marking gives its actual universal cyclic-auxiliary parameter. -/
def completeProjectiveUniversalFullParameter (hn : Nat.Coprime 4 n) (i : Fin n)
    {T : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) :
    (Over.map (base (W i) unitTwo (hΔ i))).obj T ⟶ cyclicAuxiliaryScheme n :=
  originalFaithfulParameter (W i) unitTwo (hΔ i) (CyclicLabels n)
    (completeProjectiveFullParameter K n h L a ha p q hs hn i f)

/-- Every universal label retains its original full marking through the actual comparison. -/
theorem completeProjectiveUniversalFullParameter_value (hn : Nat.Coprime 4 n) (i : Fin n)
    {T : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) (c : CyclicLabels n) :
    (completeProjectiveUniversalFullParameter K n h L a ha p q hs h2 hn i f ≫
      cyclicAuxiliaryInclusion n ≫ value universalGroup (CyclicLabels n) c).left =
        (completeProjectiveFullMarking K n h L a ha p q hs i f c).left ≫
          (originalCoefficientGroupIso (W i) unitTwo (hΔ i)).inv.hom.hom.hom.left ≫
            CategoryTheory.Limits.pullback.fst (integralCurveStructure smoothEquation)
              (base (W i) unitTwo (hΔ i)) := by
  have he := originalFaithfulParameter_value_left (W i) unitTwo (hΔ i) (CyclicLabels n)
    (completeProjectiveFullParameter K n h L a ha p q hs hn i f) c
  have hm := congrArg Over.Hom.left
    (completeProjectiveFullParameter_value K n h L a ha p q hs hn i f c)
  exact he.trans (congrArg (fun z ↦ z ≫
    (originalCoefficientGroupIso (W i) unitTwo (hΔ i)).inv.hom.hom.hom.left ≫
      CategoryTheory.Limits.pullback.fst (integralCurveStructure smoothEquation)
        (base (W i) unitTwo (hΔ i))) hm)

/-- The native original auxiliary scheme maps to the actual global full-marking scheme. -/
def completeProjectiveUniversalAuxiliaryMap (hn : Nat.Coprime 4 n) (i : Fin n) :
    (completeProjectiveAuxiliaryScheme K n h L a ha p q hs i).left ⟶
      (cyclicAuxiliaryScheme n).left :=
  (completeProjectiveUniversalFullParameter K n h L a ha p q hs h2 hn i (𝟙 _)).left

/-- The actual global map lies over the original equation's coefficient parameter. -/
@[reassoc] theorem completeProjectiveUniversalAuxiliaryMap_base
    (hn : Nat.Coprime 4 n) (i : Fin n) :
    completeProjectiveUniversalAuxiliaryMap K n h L a ha p q hs h2 hn i ≫
      (cyclicAuxiliaryScheme n).hom =
        (completeProjectiveAuxiliaryScheme K n h L a ha p q hs i).hom ≫
          base (W i) unitTwo (hΔ i) :=
  (completeProjectiveUniversalFullParameter K n h L a ha p q hs h2 hn i (𝟙 _)).w

end FLT.Mazur.PolygonInfinitesimalStages

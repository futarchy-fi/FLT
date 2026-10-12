/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonProjectiveExactTorsion
public import FLT.Mazur.AuxiliaryCoprimeFieldMarking
public import FLT.Mazur.UniversalWeierstrassCyclicAuxiliary

/-!
# Auxiliary markings retain the original polygon's cyclic orbit

On the actual auxiliary marking scheme of the constructed elliptic curve,
combine every auxiliary section with the unchanged original cyclic marking.
For n coprime to four this gives a faithful full marking on every nonempty test.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
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

/-- The constructed elliptic group on the original chosen smooth fiber. -/
def completeProjectiveGroup (i : Fin n) : CommGrp (Over (Spec (.of L))) :=
  integralCurveGroup (completeCartesianPointWeierstrass K n h L
    (Spec.map (CommRingCat.ofHom a)) p q hs i) (by
      let _ := completeCartesianPointWeierstrass_isElliptic K n h L a ha p q hs i
      exact WeierstrassCurve.isUnit_Δ _)

/-- The original constructed group is separated over its original field. -/
instance completeProjectiveGroup_separated (i : Fin n) :
    IsSeparated (completeProjectiveGroup K n h L a ha p q hs i).X.hom := by
  change IsSeparated (integralCurveStructure _)
  infer_instance

local notation "G" => completeProjectiveGroup K n h L a ha p q hs
local notation "g" => Spec.map (CommRingCat.ofHom (algebraMap L L))
local notation "φ" => completeProjectiveCyclicPointHom K n h L a ha p q hs

/-- The actual auxiliary marking open for the original constructed projective curve. -/
def completeProjectiveAuxiliaryScheme (i : Fin n) : Over (Spec (.of L)) :=
  faithfulScheme (G i).X (Labels 4)

/-- The specified test scheme maps to the unchanged field-valued marking source. -/
def completeProjectiveFieldMap (T : Over (Spec (.of L))) : T ⟶ Over.mk g :=
  Over.homMk T.hom (by simp)

/-- Every auxiliary label is combined with the actual original cyclic point. -/
def completeProjectiveFullMarking (i : Fin n) {T : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) :
    CyclicLabels n →* (T ⟶ (G i).X) :=
  coprimeFieldMarking (G i).X (Labels 4) (Multiplicative (ZMod n)) g (φ i) f
    (completeProjectiveFieldMap L T)

/-- The auxiliary and original cyclic sections are retained separately in the full marking. -/
theorem completeProjectiveFullMarking_apply (i : Fin n) {T : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i)
    (b : Labels 4) (c : Multiplicative (ZMod n)) :
    completeProjectiveFullMarking K n h L a ha p q hs i f (b, c) =
      markingOf (G i).X (Labels 4) (f ≫ faithfulInclusion (G i).X (Labels 4)) b *
        (completeProjectiveFieldMap L T ≫
          completeCartesianProjectiveMarkedPoint K n h L a ha p q hs i
            (rotateIndex c.toAdd i) : T ⟶ (G i).X) := rfl

/-- Coprimality makes the complete auxiliary and cyclic marking faithful. -/
theorem completeProjectiveFullMarking_injective (hn : Nat.Coprime 4 n) (i : Fin n)
    {T : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) [Nonempty T.left] :
    Function.Injective (completeProjectiveFullMarking K n h L a ha p q hs i f) :=
  coprimeFieldMarking_injective (G i).X (Labels 4) (Multiplicative (ZMod n)) g (φ i)
    (labels_pow 4) (fun b ↦ congrArg Multiplicative.ofAdd
      (ZModModule.char_nsmul_eq_zero n b.toAdd)) hn
    (completeProjectiveCyclicPointHom_injective K n h L a ha p q hs i) f
    (completeProjectiveFieldMap L T)

/-- The original cyclic generator still has order exactly n on every nonempty auxiliary test. -/
theorem completeProjectiveFullMarking_cyclic_order (hn : Nat.Coprime 4 n) (i : Fin n)
    {T : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) [Nonempty T.left] :
    orderOf (completeProjectiveFullMarking K n h L a ha p q hs i f (cyclicLabel n)) = n :=
  (orderOf_injective _
    (completeProjectiveFullMarking_injective K n h L a ha p q hs hn i f)
    (cyclicLabel n)).trans (cyclicLabel_order n)

end FLT.Mazur.PolygonInfinitesimalStages

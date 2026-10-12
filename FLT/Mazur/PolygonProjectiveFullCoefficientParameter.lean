/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonProjectiveCoefficientMarking

/-!
# Full original marking parameters commute with coefficient extension

Transporting the original mixed marking agrees label by label with combining
the transported auxiliary marking and the original extended cyclic marking.
The corresponding maps to faithful full-marking schemes therefore agree.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart AuxiliaryLevel UniversalWeierstrass PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  (M : Type) [Field M] [Algebra L M]
  {Y Z : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
  (r : Z ⟶ exactVeroneseProj K n h) (s : Z ⟶ Spec (.of M))
  (ht : IsPullback r s (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom ((algebraMap L M).comp a))))
local notation "aM" => RingHom.comp (algebraMap L M) a
local notation "haM" => Iff.mpr (map_ne_zero (algebraMap L M)) ha
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap L M))
local notation "eY" => completeCartesianPointProjectiveIso K n h L a ha p q hs
local notation "eZ" => completeCartesianPointProjectiveIso K n h M aM haM r s ht
local notation "W" => completeCartesianPointWeierstrass K n h L
  (Spec.map (CommRingCat.ofHom a)) p q hs
local notation "V" => completeCartesianPointWeierstrass K n h M
  (Spec.map (CommRingCat.ofHom aM)) r s ht
local notation "G" => completeProjectiveGroup K n h L a ha p q hs
local notation "H" => completeProjectiveGroup K n h M aM haM r s ht
local notation "e" => completeProjectiveCoefficientGroupIso K n h L a ha M p q hs r s ht
local notation "φ" => completeProjectiveCyclicPointHom K n h L a ha p q hs
local notation "ψ" => completeProjectiveCyclicPointHom K n h M aM haM r s ht

/-- Every auxiliary/cyclic product label survives the original coefficient comparison. -/
theorem completeProjectiveFullMarking_coefficient (i : Fin n) {T : Over (Spec (.of M))}
    (f : (Over.map b).obj T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i)
    (c : CyclicLabels n) :
    GroupMarkingCartesianTransport.marking b (G i) (H i) (e i) T
      (completeProjectiveFullMarking K n h L a ha p q hs i f) c =
        completeProjectiveFullMarking K n h M aM haM r s ht i
          (completeProjectiveAuxiliaryCoefficientParameter K n h L a ha M p q hs r s ht i f)
          c := by
  rcases c with ⟨x, y⟩
  change GroupMarkingCartesianTransport.marking b (G i) (H i) (e i) T
    ((markingOf (G i).X (Labels 4) (f ≫ faithfulInclusion (G i).X (Labels 4))).coprod
      (fieldMarkingOn (G i).X (Multiplicative (ZMod n))
        (Spec.map (CommRingCat.ofHom (algebraMap L L))) (φ i)
        (completeProjectiveFieldMap L ((Over.map b).obj T)))) (x, y) = _
  rw [GroupMarkingCartesianTransport.marking_coprod, completeProjectiveFullMarking_apply]
  congr 1
  · exact (cartesianGroupParameter_value b (G i) (H i) (e i) (Labels 4) f x).symm
  · exact completeProjectiveCyclicMarking_coefficient K n h L a ha M p q hs r s ht i T y

/-- The actual full faithful parameter map commutes with the original coefficient extension. -/
theorem completeProjectiveFullParameter_coefficient (hn : Nat.Coprime 4 n) (i : Fin n)
    {T : Over (Spec (.of M))}
    (f : (Over.map b).obj T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) :
    cartesianGroupParameter b (G i) (H i) (e i) (CyclicLabels n)
      (completeProjectiveFullParameter K n h L a ha p q hs hn i f) =
        completeProjectiveFullParameter K n h M aM haM r s ht hn i
          (completeProjectiveAuxiliaryCoefficientParameter K n h L a ha M p q hs r s ht i f)
          := by
  apply faithfulParameter_ext (H i) (CyclicLabels n)
  intro c
  rw [cartesianGroupParameter_value, completeProjectiveFullParameter_value]
  have hm : markingOf (G i).X (CyclicLabels n)
      (completeProjectiveFullParameter K n h L a ha p q hs hn i f ≫
        faithfulInclusion (G i).X (CyclicLabels n)) =
          completeProjectiveFullMarking K n h L a ha p q hs i f := by
    apply MonoidHom.ext
    intro d
    exact completeProjectiveFullParameter_value K n h L a ha p q hs hn i f d
  unfold cartesianGroupMarking
  rw [hm]
  exact completeProjectiveFullMarking_coefficient K n h L a ha M p q hs r s ht i f c

end FLT.Mazur.PolygonInfinitesimalStages

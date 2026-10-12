/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonProjectiveCoefficientGroup
public import FLT.Mazur.AuxiliaryCartesianGroupParameter
public import FLT.Mazur.PolygonProjectiveAuxiliaryParameter

/-!
# Original auxiliary and cyclic markings under coefficient extension

The actual coefficient group isomorphism transports auxiliary parameters.
The entire original cyclic marking, on every extended-field test scheme,
agrees with the independently constructed marking of the extended fiber.
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

/-- The actual auxiliary parameter transported through the original coefficient comparison. -/
def completeProjectiveAuxiliaryCoefficientParameter (i : Fin n) {T : Over (Spec (.of M))}
    (f : (Over.map b).obj T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) :
    T ⟶ completeProjectiveAuxiliaryScheme K n h M aM haM r s ht i :=
  cartesianGroupParameter b (G i) (H i) (e i) (Labels 4) f

/-- Every original cyclic label commutes with the actual coefficient group comparison. -/
theorem completeProjectiveCyclicMarking_coefficient (i : Fin n) (T : Over (Spec (.of M)))
    (c : Multiplicative (ZMod n)) :
    GroupMarkingCartesianTransport.marking b (G i) (H i) (e i) T
      (fieldMarkingOn (G i).X (Multiplicative (ZMod n))
        (Spec.map (CommRingCat.ofHom (algebraMap L L))) (φ i)
        (completeProjectiveFieldMap L ((Over.map b).obj T))) c =
      completeProjectiveFieldMap M T ≫ ψ i c := by
  apply GroupMarkingCartesianTransport.point_ext b (G i) (H i) (e i) T
  rw [GroupMarkingCartesianTransport.marking_projection]
  change (T.hom ≫ b) ≫
    (completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom a)) p q hs
      (rotateIndex c.toAdd i) ≫ (eY i).hom) =
    (T.hom ≫ (completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom aM)) r s ht
      (rotateIndex c.toAdd i) ≫ (eZ i).hom)) ≫
        (e i).inv.hom.hom.hom.left ≫
          CategoryTheory.Limits.pullback.fst (integralCurveStructure (W i)) b
  rw [completeProjectiveCoefficientGroupIso_inv_fst]
  simp only [Category.assoc]
  rw [completeProjectiveCoefficientMap_marking]

/-- Auxiliary coefficient parameters commute with all maps of original test schemes. -/
@[reassoc] theorem completeProjectiveAuxiliaryCoefficientParameter_natural
    (i : Fin n) {T U : Over (Spec (.of M))}
    (f : (Over.map b).obj T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i)
    (k : U ⟶ T) :
    k ≫ completeProjectiveAuxiliaryCoefficientParameter K n h L a ha M p q hs r s ht i f =
      completeProjectiveAuxiliaryCoefficientParameter K n h L a ha M p q hs r s ht i
        ((Over.map b).map k ≫ f) :=
  cartesianGroupParameter_natural b (G i) (H i) (e i) (Labels 4) f k

end FLT.Mazur.PolygonInfinitesimalStages

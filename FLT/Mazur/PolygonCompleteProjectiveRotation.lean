/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCartesianRotation
public import FLT.Mazur.PolygonCompleteMarkedProjectivePoints

/-!
# Actual rotations of the constructed projective elliptic curve

Transport the original fiber automorphisms along the pointed projective
isomorphism. These are scheme automorphisms with a cyclic action and the
specified marked orbit; identifying them as translations is a separate step.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeCartesianRotation

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))

/-- The original cyclic automorphism on the constructed projective cubic. -/
def completeProjectiveRotationIso (i : Fin n) (b : ZMod n) :
    integralCurve (completeCartesianPointWeierstrass K n h L
      (Spec.map (CommRingCat.ofHom a)) p q hs i) ≅
    integralCurve (completeCartesianPointWeierstrass K n h L
      (Spec.map (CommRingCat.ofHom a)) p q hs i) :=
  (completeCartesianPointProjectiveIso K n h L a ha p q hs i).symm ≪≫
    completeCartesianRotationIso K n h (Spec.map (CommRingCat.ofHom a)) p q hs b ≪≫
      completeCartesianPointProjectiveIso K n h L a ha p q hs i

/-- The transported rotation preserves the original specified field structure. -/
@[reassoc] theorem completeProjectiveRotationIso_over (i : Fin n) (b : ZMod n) :
    (completeProjectiveRotationIso K n h L a ha p q hs i b).hom ≫
      integralCurveStructure (completeCartesianPointWeierstrass K n h L
        (Spec.map (CommRingCat.ofHom a)) p q hs i) =
      integralCurveStructure (completeCartesianPointWeierstrass K n h L
        (Spec.map (CommRingCat.ofHom a)) p q hs i) := by
  dsimp only [completeProjectiveRotationIso, Iso.trans_hom, Iso.symm_hom,
    completeCartesianRotationIso]
  rw [Category.assoc, Category.assoc, completeCartesianPointProjectiveIso_over,
    completeCartesianRotation_snd]
  calc
    _ = (completeCartesianPointProjectiveIso K n h L a ha p q hs i).inv ≫
        ((completeCartesianPointProjectiveIso K n h L a ha p q hs i).hom ≫ _) :=
      congrArg ((completeCartesianPointProjectiveIso K n h L a ha p q hs i).inv ≫ ·)
        (completeCartesianPointProjectiveIso_over K n h L a ha p q hs i).symm
    _ = _ := by rw [Iso.inv_hom_id_assoc]

/-- The original point isomorphism intertwines the actual geometric rotations. -/
@[reassoc] theorem completePointProjectiveIso_rotation (i : Fin n) (b : ZMod n) :
    (completeCartesianPointProjectiveIso K n h L a ha p q hs i).hom ≫
        (completeProjectiveRotationIso K n h L a ha p q hs i b).hom =
      completeCartesianRotation K n h (Spec.map (CommRingCat.ofHom a)) p q hs b ≫
        (completeCartesianPointProjectiveIso K n h L a ha p q hs i).hom := by
  simp only [completeProjectiveRotationIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc, completeCartesianRotationIso]

/-- The zero label fixes the whole original constructed cubic. -/
@[simp] theorem completeProjectiveRotationIso_zero (i : Fin n) :
    (completeProjectiveRotationIso K n h L a ha p q hs i 0).hom = 𝟙 _ := by
  simp only [completeProjectiveRotationIso, Iso.trans_hom, Iso.symm_hom,
    completeCartesianRotationIso, completeCartesianRotation_zero, Category.id_comp,
    Iso.inv_hom_id]

/-- The original addition law is retained as composition of cubic automorphisms. -/
theorem completeProjectiveRotationIso_add (i : Fin n) (b c : ZMod n) :
    (completeProjectiveRotationIso K n h L a ha p q hs i (b + c)).hom =
      (completeProjectiveRotationIso K n h L a ha p q hs i b).hom ≫
        (completeProjectiveRotationIso K n h L a ha p q hs i c).hom := by
  simp only [completeProjectiveRotationIso, Iso.trans_hom, Iso.symm_hom,
    completeCartesianRotationIso, completeCartesianRotation_add, Category.assoc,
    Iso.hom_inv_id_assoc]

/-- Every original marked field point is carried to its original shifted label. -/
@[reassoc] theorem completeProjectiveMarkedPoint_rotation (i j : Fin n) (b : ZMod n) :
    (completeCartesianProjectiveMarkedPoint K n h L a ha p q hs i j).left ≫
        (completeProjectiveRotationIso K n h L a ha p q hs i b).hom =
      (completeCartesianProjectiveMarkedPoint K n h L a ha p q hs i (rotateIndex b j)).left := by
  change (_ ≫ (completeCartesianPointProjectiveIso K n h L a ha p q hs i).hom) ≫ _ =
    _ ≫ (completeCartesianPointProjectiveIso K n h L a ha p q hs i).hom
  rw [Category.assoc, completePointProjectiveIso_rotation,
    completeCartesianMarking_rotation_assoc]

end FLT.Mazur.PolygonInfinitesimalStages

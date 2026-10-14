/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothFieldCoefficientGroup
public import FLT.Mazur.PolygonCompleteSmoothFieldCurve
public import FLT.Mazur.GeneralizedCurveBaseChangeIso

/-!
# The full original smooth DR curve commutes with coefficient extension

The constructed group comparison also preserves the whole-curve action and
smooth inclusion. Thus the original coefficient square gives a full DR
isomorphism with the actual base change, retaining its original projection.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
  (M : Type) [Field M] [Algebra L M]
  {Z : Scheme} (r : Z ⟶ exactVeroneseProj K n h) (s : Z ⟶ Spec (.of M))
  (ht : IsPullback r s (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom ((algebraMap L M).comp a))))
local notation "aM" => RingHom.comp (algebraMap L M) a
local notation "haM" => Iff.mpr (map_ne_zero (algebraMap L M)) ha
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap L M))
local notation "E" => completeFieldGeneralizedCurve K n h L a ha p q hs
local notation "D" => completeFieldGeneralizedCurve K n h M aM haM r s ht
local notation "u" => completeCartesianBaseMap K n h
  (Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom aM)) p q hs r s ht b
  (completeCoefficientSpec_comp K L a M)

/-- The full DR curve on the original extended square is the actual base-changed DR object. -/
irreducible_def completeFieldCoefficientCurveIso (i : Fin n) : (E i).baseChange b ≅ D i := by
  let g := completeFieldCoefficientGroupIso K n h L a ha p q hs M r s ht i
  let e : ((E i).baseChange b).group ≅ (D i).group :=
    (CommGrp.forget (Over (Spec (.of M)))).mapIso g
  let _ : IsMonHom e.hom := inferInstanceAs (IsMonHom g.hom.hom.hom.hom)
  refine GeneralizedEllipticCurve.isoMk e e ?_ ?_
  · rw [baseChange_inclusion, pullbackInclusion,
      completeFieldGeneralizedCurve_inclusion, completeFieldGeneralizedCurve_inclusion]
    change (Over.pullback b).map (𝟙 (Over.mk q)) ≫ e.hom = e.hom ≫ 𝟙 _
    rw [(Over.pullback b).map_id, Category.id_comp, Category.comp_id]
  · exact IsMonHom.mul_hom e.hom

/-- The full DR isomorphism retains exactly the actual original coefficient projection. -/
@[reassoc] theorem completeFieldCoefficientCurveIso_inv_fst (i : Fin n) :
    (completeFieldCoefficientCurveIso K n h L a ha p q hs M r s ht i).inv.curve.left ≫
      pullback.fst q b = u := by
  rw [completeFieldCoefficientCurveIso_def]
  exact completeFieldCoefficientGroupIso_inv_fst K n h L a ha p q hs M r s ht i

/-- The coefficient projection retains every original marking, not only the DR identity. -/
@[reassoc] theorem completeFieldCoefficientCurveIso_marking (i j : Fin n) :
    completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom aM)) r s ht j ≫
      (completeFieldCoefficientCurveIso K n h L a ha p q hs M r s ht i).inv.curve.left ≫
        pullback.fst q b =
          b ≫ completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom a)) p q hs j := by
  rw [completeFieldCoefficientCurveIso_inv_fst, completeCartesianBaseMap_marking]

end FLT.Mazur.PolygonInfinitesimalStages

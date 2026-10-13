/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothFieldGroup
public import FLT.Mazur.PolygonProjectiveCoefficientGroup
public import FLT.Mazur.GroupSchemeBaseChangeProjections

/-!
# Coefficient extension of the full original smooth field group

The cubic comparison transports the actual monoidal pullback group to the
independently specified original extended-field square. Its projection is the
original Cartesian map, not a newly chosen isomorphism of unmarked curves.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))

/-- The bundled full group on the actual original smooth field curve. -/
def completeFieldGroup (i : Fin n) : CommGrp (Over (Spec (.of L))) := by
  let _ := completeFieldCommGrp K n h L a ha p q hs i
  exact CommGrp.mk (Over.mk q)

/-- The original projective comparison is an isomorphism of the constructed groups. -/
def completeFieldCubicGroupIso (i : Fin n) :
    completeFieldGroup K n h L a ha p q hs i ≅ completeProjectiveGroup K n h L a ha p q hs i := by
  let _ := completeFieldCubicCommGrp K n h L a ha p q hs i
  let _ := completeFieldCommGrp K n h L a ha p q hs i
  let e := completeFieldCubicOverIso K n h L a ha p q hs i
  let _ : IsMonHom e.inv := isMonHom_ofIso e.symm
  let _ : IsMonHom e.hom := inferInstanceAs (IsMonHom e.symm.inv)
  exact CommGrp.mkIso' e

/-- The group comparison retains the actual original projective map. -/
theorem completeFieldCubicGroupIso_hom (i : Fin n) :
    (completeFieldCubicGroupIso K n h L a ha p q hs i).hom.hom.hom.hom.left =
      (completeCartesianPointProjectiveIso K n h L a ha p q hs i).hom := rfl

/-- The inverse retains the actual original projective inverse. -/
theorem completeFieldCubicGroupIso_inv (i : Fin n) :
    (completeFieldCubicGroupIso K n h L a ha p q hs i).inv.hom.hom.hom.left =
      (completeCartesianPointProjectiveIso K n h L a ha p q hs i).inv := rfl

variable (M : Type) [Field M] [Algebra L M]
  {Z : Scheme} (r : Z ⟶ exactVeroneseProj K n h) (s : Z ⟶ Spec (.of M))
  (ht : IsPullback r s (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom ((algebraMap L M).comp a))))
local notation "aM" => RingHom.comp (algebraMap L M) a
local notation "haM" => Iff.mpr (map_ne_zero (algebraMap L M)) ha
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap L M))
local notation "u" => completeCartesianBaseMap K n h
  (Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom aM)) p q hs r s ht b
  (completeCoefficientSpec_comp K L a M)

/-- The original full field groups commute with the given coefficient extension. -/
irreducible_def completeFieldCoefficientGroupIso (i : Fin n) :
    (Over.pullback b).mapCommGrp.obj (completeFieldGroup K n h L a ha p q hs i) ≅
      completeFieldGroup K n h M aM haM r s ht i :=
  (Over.pullback b).mapCommGrp.mapIso (completeFieldCubicGroupIso K n h L a ha p q hs i) ≪≫
    completeProjectiveCoefficientGroupIso K n h L a ha M p q hs r s ht i ≪≫
      (completeFieldCubicGroupIso K n h M aM haM r s ht i).symm

/-- Forgetting the extended group law recovers the original Cartesian refinement projection. -/
@[reassoc] theorem completeFieldCoefficientGroupIso_inv_fst (i : Fin n) :
    (completeFieldCoefficientGroupIso K n h L a ha p q hs M r s ht i).inv.hom.hom.hom.left ≫
      pullback.fst q b = u := by
  rw [completeFieldCoefficientGroupIso_def]
  change (completeFieldCubicGroupIso K n h M aM haM r s ht i).hom.hom.hom.hom.left ≫
    (completeProjectiveCoefficientGroupIso K n h L a ha M p q hs r s ht i).inv.hom.hom.hom.left ≫
      ((Over.pullback b).mapCommGrp.map
        (completeFieldCubicGroupIso K n h L a ha p q hs i).inv).hom.hom.hom.left ≫
          pullback.fst q b = _
  erw [GroupSchemeBaseChange.map_hom_fst]
  erw [completeProjectiveCoefficientGroupIso_inv_fst_assoc K n h L a ha M p q hs r s ht i]
  rw [completeFieldCubicGroupIso_hom, completeFieldCubicGroupIso_inv]
  change (completeCartesianPointProjectiveIso K n h M aM haM r s ht i).hom ≫
    ((completeCartesianPointProjectiveIso K n h M aM haM r s ht i).inv ≫ u ≫
      (completeCartesianPointProjectiveIso K n h L a ha p q hs i).hom) ≫
        (completeCartesianPointProjectiveIso K n h L a ha p q hs i).inv = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.PolygonInfinitesimalStages

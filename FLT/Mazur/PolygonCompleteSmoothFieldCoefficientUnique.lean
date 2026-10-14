/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothFieldCoefficientCurve
public import FLT.Mazur.GeneralizedCurveBaseChangeCoherence

/-!
# Uniqueness of the original full field coefficient comparison

The two original Cartesian projections determine the comparison in the full
DR category. Its inverse is the canonical isomorphism of the retained square.
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

/-- Original total-space projections detect all full DR maps into a pulled original curve. -/
theorem completeFieldBaseChange_hom_ext (i : Fin n)
    {T : Scheme} (b : T ⟶ Spec (.of L)) (D : GeneralizedEllipticCurve T)
    (f g : D ⟶ (completeFieldGeneralizedCurve K n h L a ha p q hs i).baseChange b)
    (hf : f.curve.left ≫ pullback.fst q b ≫ p =
      g.curve.left ≫ pullback.fst q b ≫ p) : f = g := by
  apply baseChange_hom_ext b
  change f.curve.left ≫ pullback.fst q b = g.curve.left ≫ pullback.fst q b
  apply hs.hom_ext
  · simpa only [Category.assoc] using hf
  · change f.curve.left ≫ pullback.fst q b ≫ q =
      g.curve.left ≫ pullback.fst q b ≫ q
    rw [pullback.condition, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ b) (f.curve.w.trans g.curve.w.symm)

variable (M : Type) [Field M] [Algebra L M]
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

local notation "e" => completeFieldCoefficientCurveIso K n h L a ha p q hs M r s ht

/-- The inverse retains the actual map to the complete total space. -/
@[reassoc] theorem completeFieldCoefficientCurveIso_inv_total (i : Fin n) :
    (e i).inv.curve.left ≫ pullback.fst q b ≫ p = r := by
  rw [completeFieldCoefficientCurveIso_inv_fst_assoc, completeCartesianBaseMap_fst]

/-- The original total-space projection determines the full coefficient comparison uniquely. -/
theorem completeFieldCoefficientCurveIso_unique (i : Fin n)
    (d : (E i).baseChange b ≅ D i)
    (hd : d.inv.curve.left ≫ pullback.fst q b ≫ p = r) : d = e i := by
  apply Iso.symm_eq_iff.mp
  apply Iso.ext
  apply completeFieldBaseChange_hom_ext K n h L a ha p q hs i
  exact hd.trans (completeFieldCoefficientCurveIso_inv_total K n h L a ha p q hs
    M r s ht i).symm

/-- On schemes the inverse is exactly the canonical comparison of the original pullback square. -/
theorem completeFieldCoefficientCurveIso_inv_canonical (i : Fin n) :
    (e i).inv.curve.left =
      (completeCartesianBaseMap_isPullback K n h _ _ p q hs r s ht b
        (completeCoefficientSpec_comp K L a M)).isoPullback.hom := by
  apply pullback.hom_ext (f := q) (g := b)
  · rw [completeFieldCoefficientCurveIso_inv_fst, IsPullback.isoPullback_hom_fst]
  · exact (e i).inv.curve.w.trans (IsPullback.isoPullback_hom_snd _).symm

end FLT.Mazur.PolygonInfinitesimalStages

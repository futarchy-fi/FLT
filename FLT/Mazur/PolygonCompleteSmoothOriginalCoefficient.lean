/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothOriginalCurveIso
public import FLT.Mazur.PolygonCompleteSmoothFieldCoefficientUnique
public import FLT.Mazur.GeneralizedCurveBaseChangeCompEq

/-!
# Coefficient coherence of the original smooth DR comparison

The comparison with the complete family commutes with the pre-existing full
field coefficient isomorphism. Equality is checked on the original projections.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
/-- Two successive original curve projections detect maps into an iterated DR pullback. -/
theorem completeIteratedBaseChange_hom_ext {S T U : Scheme}
    (A : GeneralizedEllipticCurve S) (u : T ⟶ S) (b : U ⟶ T)
    {D : GeneralizedEllipticCurve U}
    (f g : D ⟶ (A.baseChange u).baseChange b)
    (hh : f.curve.left ≫ pullback.fst (A.baseChange u).curve.hom b ≫
        pullback.fst A.curve.hom u =
      g.curve.left ≫ pullback.fst (A.baseChange u).curve.hom b ≫
        pullback.fst A.curve.hom u) : f = g := by
  apply baseChange_hom_ext b
  apply pullback.hom_ext
  · simpa only [Category.assoc] using hh
  · change f.curve.left ≫ pullback.fst (pullback.snd A.curve.hom u) b ≫
        pullback.snd A.curve.hom u =
      g.curve.left ≫ pullback.fst (pullback.snd A.curve.hom u) b ≫
        pullback.snd A.curve.hom u
    rw [pullback.condition, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ b) (f.curve.w.trans g.curve.w.symm)

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
local notation "u" => Spec.map (CommRingCat.ofHom a)
local notation "v" => Spec.map (CommRingCat.ofHom aM)
local notation "E" => completeGeneralizedCurve K n h
local notation "eL" => completeSmoothOriginalCurveIso K n h L a ha p q hs
local notation "eM" => completeSmoothOriginalCurveIso K n h M aM haM r s ht
local notation "eLM" => completeFieldCoefficientCurveIso K n h L a ha p q hs M r s ht 0
local notation "d" => GeneralizedEllipticCurve.baseChangeCompEqIso (E) u b v
  (Eq.symm (completeCoefficientSpec_comp K L a M))

/-- The original full smooth DR comparison commutes with extension of the field coefficients. -/
theorem completeSmoothOriginalCurveIso_coefficient :
    (eLM).inv ≫ (baseChangeFunctor b).map (eL).hom = (eM).hom ≫ (d).hom := by
  let f := (eLM).inv ≫ (baseChangeFunctor b).map (eL).hom
  let g := (eM).hom ≫ (d).hom
  have hf : f.curve.left ≫ pullback.fst ((E).baseChange u).curve.hom b ≫
      pullback.fst (E).curve.hom u = r := by
    change ((eLM).inv.curve.left ≫ (baseChangeMap b (eL).hom).curve.left) ≫ _ = _
    rw [Category.assoc, baseChangeMap_fst_assoc, completeSmoothOriginalCurveIso_fst]
    exact completeFieldCoefficientCurveIso_inv_total K n h L a ha p q hs M r s ht 0
  have hg : g.curve.left ≫ pullback.fst ((E).baseChange u).curve.hom b ≫
      pullback.fst (E).curve.hom u = r := by
    change ((eM).hom.curve.left ≫ (d).hom.curve.left) ≫ _ = _
    rw [Category.assoc, baseChangeCompEqIso_curve_fst, completeSmoothOriginalCurveIso_fst]
  exact completeIteratedBaseChange_hom_ext (E) u b f g (hf.trans hg.symm)

end FLT.Mazur.PolygonInfinitesimalStages

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedGenus
public import FLT.Mazur.PolygonFieldExtension

/-!
# Actual field fibers that kill the original parameter

A coefficient map killing the original power-series variable factors through
constant coefficients. Pasting the actual closed square retains the original
polygon pinching presentation on every such field fiber.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L)

/-- Killing the original parameter forces factorization through constant coefficients. -/
theorem completeCoefficient_factor (ha : a PowerSeries.X = 0) :
    a = (a.comp PowerSeries.C).comp PowerSeries.constantCoeff := by
  ext f
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.mpr
    (show PowerSeries.constantCoeff (f - PowerSeries.C (PowerSeries.constantCoeff f)) = 0 by
      simp)
  have he := congrArg a hg
  simpa only [map_sub, map_mul, ha, zero_mul, sub_eq_zero, RingHom.comp_apply] using he

/-- Every actual field fiber killing q retains the original polygon cocone. -/
theorem completeZeroParameterFiber_exists_cocone (ha : a PowerSeries.X = 0)
    {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
    (hp : IsPullback p q (exactVeroneseProjToBase K n h)
      (Spec.map (CommRingCat.ofHom a))) :
    ∃ (u : PolygonPinching.components L n ⟶ Over.mk q)
      (v : PolygonPinching.nodes L n ⟶ Over.mk q),
      IsPushout (PolygonPinching.toComponents L n (by omega))
        (PolygonPinching.toNodes L n) u v := by
  let b := Spec.map (CommRingCat.ofHom (a.comp PowerSeries.C))
  have hab : b ≫ completeClosedBase K = Spec.map (CommRingCat.ofHom a) := by
    rw [completeClosedBase, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (completeCoefficient_factor K L a ha).symm
  have hs := (IsPullback.of_hasPullback
    (PolygonCyclicAtlas.toBase K n h) b).paste_horiz (completeClosedFiber_isPullback K n h)
  rw [hab] at hs
  let e := hs.isoPullback ≪≫ hp.isoPullback.symm
  obtain ⟨u, v, huv⟩ := PolygonFieldExtension.exists_cocone_of_isPullback K L n (by omega)
    (PolygonCyclicAtlas.normalization K n h) (PolygonCyclicAtlas.nodes K n h)
    (PolygonCyclicPushout.isPushout K n h (by omega)) b _ _
    (IsPullback.of_hasPullback (PolygonCyclicAtlas.toBase K n h) b)
  let eo : Over.mk (pullback.snd (PolygonCyclicAtlas.toBase K n h) b) ≅ Over.mk q :=
    Over.isoMk e (by
      dsimp [e]
      rw [Category.assoc, IsPullback.isoPullback_inv_snd, IsPullback.isoPullback_hom_snd])
  exact ⟨u ≫ eo.hom, v ≫ eo.hom, huv.of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) eo
    (by simp) (by simp) (by simp) (by simp)⟩

end FLT.Mazur.PolygonInfinitesimalStages

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSmoothEtaleCoordinates
public import FLT.Mazur.PolynomialGeometricRationalPoints

/-!
# Separable representatives in geometric opens of smooth schemes

Every nonempty geometric open in a smooth scheme over a field contains a
rational geometric point descending to the relative separable closure.
The construction retains both structural field maps and the original open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SmoothGeometricSeparablePoints
set_option backward.isDefEq.respectTransparency false
variable {k K : Type} [Field k] [Field K] [IsSepClosed K] [Algebra k K]
  {X Y : Scheme}

/-- Separable original points meet every nonempty open after geometric base change. -/
theorem exists_point (f : X ⟶ Spec (.of k)) [Smooth f]
    (a : Y ⟶ X) (b : Y ⟶ Spec (.of K))
    (H : IsPullback a b f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (W : Set Y) (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ (y : Spec (.of (separableClosure k K)) ⟶ X) (z : Spec (.of K) ⟶ Y),
      z default ∈ W ∧ z ≫ b = 𝟙 _ ∧
        y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (separableClosure k K))) ∧
        z ≫ a = Spec.map (CommRingCat.ofHom (algebraMap (separableClosure k K) K)) ≫ y := by
  obtain ⟨w, hw⟩ := hne
  obtain ⟨A, n, g, j, hg, hj, hx, hf⟩ :=
    AffineSmoothEtaleCoordinates.exists_chart f (a w)
  let _ := hj
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, _, hv⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback j a) u w hu
  have HC : IsPullback (pullback.fst j a) (pullback.snd j a ≫ b)
      (Spec.map (CommRingCat.ofHom (g.comp MvPolynomial.C)))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    have h := (IsPullback.of_hasPullback j a).paste_vert H
    rw [hf, ← Spec.map_comp] at h
    exact h
  let HP := PolynomialCoefficientCartesian.chart_isPullback (K := K) g
  let e := HP.isoIsPullback _ _ HC
  let m := e.hom ≫ pullback.snd j a
  have hne' : (m ⁻¹' W).Nonempty := by
    refine ⟨e.inv v, ?_⟩
    change (e.inv ≫ e.hom ≫ pullback.snd j a) v ∈ W
    rw [e.inv_hom_id_assoc, hv]
    exact hw
  obtain ⟨q₀, z, hzW, hzA, hzK, hq₀⟩ :=
    PolynomialGeometricRationalPoints.exists_point g hg (m ⁻¹' W)
      (hW.preimage m.continuous) hne'
  refine ⟨Spec.map (CommRingCat.ofHom q₀) ≫ j, z ≫ m, hzW, ?_, ?_, ?_⟩
  · change z ≫ (e.hom ≫ pullback.snd j a) ≫ b = _
    rw [Category.assoc e.hom, HP.isoIsPullback_hom_snd _ _ HC]
    exact hzK
  · rw [Category.assoc, hf, ← Spec.map_comp, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (q₀.comp (g.comp MvPolynomial.C))) = _
    rw [hq₀]
  · change (z ≫ e.hom ≫ pullback.snd j a) ≫ a = _
    rw [Category.assoc, Category.assoc, ← pullback.condition,
      ← Category.assoc e.hom, HP.isoIsPullback_hom_fst _ _ HC,
      ← Category.assoc, hzA]
    rw [← Category.assoc, ← Spec.map_comp]
    rfl

end FLT.Mazur.SmoothGeometricSeparablePoints

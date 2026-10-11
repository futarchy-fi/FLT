/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothGeometricSeparablePoints

/-!
# Separable fiber representatives retain a point in the specified open

A nonempty open of a geometric smooth fiber supplies a separable original
translation and a rational geometric point of that very open. This applies
to full chart intersections without identifying them with prescribed graphs.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SmoothFiberSeparablePoints
set_option backward.isDefEq.respectTransparency false
variable {R k K : Type} [CommRing R] [Field k] [Field K] [IsSepClosed K] [Algebra k K]
  {V Y U : Scheme}

/-- A point in the original open retains its separable translation and its geometric base. -/
theorem exists_point (f : V ⟶ Spec (.of R)) [Smooth f] (φ : R →+* k)
    (a : Y ⟶ V) (b : Y ⟶ Spec (.of K))
    (H : IsPullback a b f
      (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ))))
    (j : U ⟶ Y) [IsOpenImmersion j] (hne : Nonempty U) :
    ∃ (y : Spec (.of (separableClosure k K)) ⟶ V) (u : Spec (.of K) ⟶ U),
      y ≫ f = Spec.map
        (CommRingCat.ofHom ((algebraMap k (separableClosure k K)).comp φ)) ∧
      u ≫ j ≫ b = 𝟙 _ ∧
      u ≫ j ≫ a = Spec.map
        (CommRingCat.ofHom (algebraMap (separableClosure k K) K)) ≫ y := by
  let t := Spec.map (CommRingCat.ofHom φ)
  let c := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let p := pullback.snd f t
  have HP : IsPullback (pullback.fst p c ≫ pullback.fst f t) (pullback.snd p c) f
      (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ))) := by
    have h := (IsPullback.of_hasPullback p c).paste_horiz
      (IsPullback.of_hasPullback f t)
    simpa only [c, t, ← Spec.map_comp, CommRingCat.ofHom_comp] using h
  let e := HP.isoIsPullback _ _ H
  let W := e.hom ⁻¹' Set.range j
  have hW : IsOpen W := j.isOpenEmbedding.isOpen_range.preimage e.hom.continuous
  have hnW : W.Nonempty := by
    obtain ⟨v⟩ := hne
    refine ⟨e.inv (j v), ?_⟩
    change (e.inv ≫ e.hom) (j v) ∈ Set.range j
    rw [e.inv_hom_id]
    exact ⟨v, rfl⟩
  obtain ⟨y, z, hzW, hzK, hy, hz⟩ := SmoothGeometricSeparablePoints.exists_point p
    (pullback.fst p c) (pullback.snd p c) (IsPullback.of_hasPullback p c) W hW hnW
  have hr : Set.range (z ≫ e.hom) ⊆ Set.range j := by
    rintro _ ⟨w, rfl⟩
    simpa only [W, Set.mem_preimage, Scheme.Hom.comp_apply, Subsingleton.elim w default] using hzW
  let u := IsOpenImmersion.lift j (z ≫ e.hom) hr
  have hu : u ≫ j = z ≫ e.hom := IsOpenImmersion.lift_fac j _ hr
  refine ⟨y ≫ pullback.fst f t, u, ?_, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hy, ← Spec.map_comp]
    rfl
  · rw [← Category.assoc, hu, Category.assoc, HP.isoIsPullback_hom_snd _ _ H]
    exact hzK
  · rw [← Category.assoc, hu, Category.assoc, HP.isoIsPullback_hom_fst _ _ H,
      ← Category.assoc, hz, Category.assoc]

end FLT.Mazur.SmoothFiberSeparablePoints

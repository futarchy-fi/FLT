/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothLocusSpec
public import FLT.Mathlib.RingTheory.Smooth.PointwiseDescent
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# Smooth loci under field extensions

Smoothness at an individual point both ascends and descends under an
arbitrary extension of the ground field. Affine source charts give the
corresponding equality on the actual scheme pullback.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- The affine smooth-locus equality after a field extension. -/
theorem Spec.preimage_smoothLocus_fieldExtension
    {K L A : Type u} [Field K] [Field L] [CommRing A]
    [Algebra K L] [Algebra K A] [Algebra.FinitePresentation K A] :
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K A)))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⁻¹ᵁ
      (Spec.map (CommRingCat.ofHom (algebraMap K A))).smoothLocus =
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K A)))
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))).smoothLocus := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap K A))
  let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let e := pullbackSymmetry f g ≪≫ pullbackSpecIso K L A
  ext z
  obtain ⟨q, rfl⟩ := e.inv.homeomorph.surjective z
  change (e.inv ≫ pullback.fst f g) q ∈ f.smoothLocus ↔
    q ∈ e.inv ⁻¹ᵁ (pullback.snd f g).smoothLocus
  rw [Scheme.Hom.preimage_smoothLocus_eq]
  have h₁ : e.inv ≫ pullback.fst f g =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[K] TensorProduct K L A).toRingHom) := by
    simp [e, f, g]
  have h₂ : e.inv ≫ pullback.snd f g =
      Spec.map (CommRingCat.ofHom (algebraMap L (TensorProduct K L A))) := by
    simp only [e, Iso.trans_inv, Category.assoc, pullbackSymmetry_inv_comp_snd]
    exact pullbackSpecIso_inv_fst K L A
  rw [h₁]
  rw! [h₂]
  change PrimeSpectrum.comap
    (Algebra.TensorProduct.includeRight : A →ₐ[K] TensorProduct K L A).toRingHom q ∈
    (Spec.map (CommRingCat.ofHom (algebraMap K A))).smoothLocus ↔
      q ∈ (Spec.map (CommRingCat.ofHom (algebraMap L (TensorProduct K L A)))).smoothLocus
  rw [Spec.mem_smoothLocus_iff (R := K) (S := A),
    Spec.mem_smoothLocus_iff (R := L) (S := TensorProduct K L A)]
  constructor
  · intro h
    have : Algebra.IsSmoothAt K
        (q.asIdeal.comap (Algebra.TensorProduct.includeRight : A →ₐ[K] TensorProduct K L A)) := h
    exact Algebra.IsSmoothAt.flat_tensorProduct (R := K) (S := A) (T := L) q.asIdeal
  · intro h
    have : Algebra.IsSmoothAt L q.asIdeal := h
    exact Algebra.IsSmoothAt.of_fieldExtension (K := K) (L := L) (A := A) q.asIdeal


/-- Smooth loci of locally finitely presented schemes over a field commute
with every extension of that field. -/
theorem Scheme.Hom.preimage_smoothLocus_fieldExtension
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    (g : Spec (.of L) ⟶ Spec (.of K)) :
    pullback.fst f g ⁻¹ᵁ f.smoothLocus = (pullback.snd f g).smoothLocus := by
  wlog hX : ∃ S, X = Spec S generalizing X
  · ext z
    obtain ⟨x, hx⟩ := X.affineCover.covers (pullback.fst f g z)
    let i := X.affineCover.f (X.affineCover.idx (pullback.fst f g z))
    change i x = pullback.fst f g z at hx
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback x z hx
    let e := pullbackRightPullbackFstIso f g i
    let j := e.inv ≫ pullback.snd i (pullback.fst f g)
    have hjopen : IsOpenImmersion j := by dsimp [j]; infer_instance
    have hj₁ : j ≫ pullback.fst f g = pullback.fst (i ≫ f) g ≫ i := by simp [j, e]
    have hj₂ : j ≫ pullback.snd f g = pullback.snd (i ≫ f) g := by simp [j, e]
    have he : j (e.hom w) = z := by
      change (e.hom ≫ j) w = z
      simpa [j] using hw₂
    have H := this (i ≫ f) ⟨_, rfl⟩
    rw [← he]
    change (j ≫ pullback.fst f g) (e.hom w) ∈ f.smoothLocus ↔
      e.hom w ∈ j ⁻¹ᵁ (pullback.snd f g).smoothLocus
    rw [hj₁]
    change pullback.fst (i ≫ f) g (e.hom w) ∈ i ⁻¹ᵁ f.smoothLocus ↔ _
    rw [Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.preimage_smoothLocus_eq]
    rw! [hj₂]
    exact (congrArg (fun U ↦ e.hom w ∈ U) H).to_iff
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨S, hS⟩ := S
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  have hfp := (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp
    ‹LocallyOfFinitePresentation (Spec.map φ)›
  algebraize [φ.hom, ψ.hom]
  exact Spec.preimage_smoothLocus_fieldExtension (K := K) (L := L) (A := S)

end AlgebraicGeometry

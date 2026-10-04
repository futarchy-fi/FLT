/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothLocusAffineFiber
public import FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothLocusFiberCharts

/-!
# The pointwise smooth-fibre criterion for schemes

For a flat locally finitely presented morphism, its smooth locus restricts
on each canonical fibre to the smooth locus over the residue field.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- The smooth locus of a flat locally finitely presented morphism restricts
to the smooth locus of each canonical fibre over its residue field. -/
theorem Scheme.Hom.preimage_smoothLocus_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] (y : Y) :
    f.fiberι y ⁻¹ᵁ f.smoothLocus = (f.fiberToSpecResidueField y).smoothLocus := by
  wlog hY : ∃ R, Y = Spec R generalizing X Y
  · obtain ⟨y', hy'⟩ := Y.affineCover.covers y
    let g := Y.affineCover.f (Y.affineCover.idx y)
    change g y' = y at hy'
    rw [← hy']
    let b := pullback.snd f g
    let a := pullback.fst f g
    let h := IsPullback.of_hasPullback f g
    let e := Scheme.Hom.fiberMapOfIsPullback h y'
    have he : IsIso e := inferInstance
    have H := this b y' ⟨_, rfl⟩
    ext z
    obtain ⟨z', rfl⟩ := e.homeomorph.surjective z
    have h₁ := Scheme.Hom.preimage_smoothLocus_openBase h
    have h₂ := Scheme.Hom.preimage_smoothLocus_fiberMapOfIsPullback h y'
    change f.fiberι (g y') (e z') ∈ f.smoothLocus ↔
      e z' ∈ (f.fiberToSpecResidueField (g y')).smoothLocus
    change (e ≫ f.fiberι (g y')) z' ∈ f.smoothLocus ↔ _
    rw [Scheme.Hom.fiberMapOfIsPullback_fiberι]
    change b.fiberι y' z' ∈ a ⁻¹ᵁ f.smoothLocus ↔
      z' ∈ e ⁻¹ᵁ (f.fiberToSpecResidueField (g y')).smoothLocus
    rw [h₁, h₂]
    exact (congrArg (fun U ↦ z' ∈ U) H).to_iff
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S generalizing X
  · ext z
    obtain ⟨x, hx⟩ := X.affineCover.covers (f.fiberι y z)
    let i := X.affineCover.f (X.affineCover.idx (f.fiberι y z))
    change i x = f.fiberι y z at hx
    have hxy : (i ≫ f) x = y := by
      rw [Scheme.Hom.comp_apply, hx]
      have hz : f.fiberι y z ∈ f ⁻¹' {y} := by
        rw [← f.range_fiberι y]
        exact ⟨z, rfl⟩
      exact hz
    obtain ⟨z', hz'⟩ : x ∈ Set.range ((i ≫ f).fiberι y) := by
      rw [Scheme.Hom.range_fiberι]
      exact hxy
    have he : f.fiberPrecomp i y z' = z := by
      apply (f.fiberι y).isEmbedding.injective
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.fiberPrecomp_fiberι,
        Scheme.Hom.comp_apply, hz', hx]
    have H := this (i ≫ f) ⟨_, rfl⟩
    rw [← he]
    change (f.fiberPrecomp i y ≫ f.fiberι y) z' ∈ f.smoothLocus ↔ _
    rw [Scheme.Hom.fiberPrecomp_fiberι]
    change (i ≫ f).fiberι y z' ∈ i ⁻¹ᵁ f.smoothLocus ↔
      z' ∈ f.fiberPrecomp i y ⁻¹ᵁ (f.fiberToSpecResidueField y).smoothLocus
    rw [Scheme.Hom.preimage_smoothLocus_eq,
      Scheme.Hom.preimage_smoothLocus_fiberPrecomp]
    exact (congrArg (fun U ↦ z' ∈ U) H).to_iff
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have hflat := (HasRingHomProperty.Spec_iff (P := @Flat)).mp ‹Flat (Spec.map φ)›
  have hfp := (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp
    ‹LocallyOfFinitePresentation (Spec.map φ)›
  algebraize [φ.hom]
  exact Spec.preimage_smoothLocus_fiberι y

end AlgebraicGeometry

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothLocusGlobalFiber
public import FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothLocusFieldExtension

/-!
# Smooth loci commute with arbitrary base change

For flat locally finitely presented scheme maps, the canonical fibre
criterion reduces arbitrary base change to extension of residue fields.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- The field-extension formula on any Cartesian square. -/
theorem Scheme.Hom.preimage_smoothLocus_fieldExtension_of_isPullback
    {K L : Type u} [Field K] [Field L] {X P : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} {g : Spec (.of L) ⟶ Spec (.of K)}
    {a : P ⟶ X} {b : P ⟶ Spec (.of L)} (h : IsPullback a b f g)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation b] :
    a ⁻¹ᵁ f.smoothLocus = b.smoothLocus := by
  calc
    a ⁻¹ᵁ f.smoothLocus =
        h.isoPullback.hom ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ f.smoothLocus) := by
      rw [← Scheme.Hom.comp_preimage, h.isoPullback_hom_fst]
    _ = h.isoPullback.hom ⁻¹ᵁ (pullback.snd f g).smoothLocus := by
      rw [Scheme.Hom.preimage_smoothLocus_fieldExtension]
    _ = b.smoothLocus := by
      rw [Scheme.Hom.preimage_smoothLocus_eq]
      congr 1
      exact h.isoPullback_hom_snd

/-- The smooth locus of a flat locally finitely presented morphism commutes
with arbitrary scheme base change. -/
theorem Scheme.Hom.preimage_smoothLocus_baseChange {X S T : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] (g : T ⟶ S) :
    pullback.fst f g ⁻¹ᵁ f.smoothLocus = (pullback.snd f g).smoothLocus := by
  let b := pullback.snd f g
  let h := IsPullback.of_hasPullback f g
  ext z
  change pullback.fst f g z ∈ f.smoothLocus ↔ z ∈ b.smoothLocus
  let y := b z
  let z' := b.asFiber z
  have H := Scheme.Hom.preimage_smoothLocus_fieldExtension_of_isPullback
    (Scheme.Hom.isPullback_fiberMapOfIsPullback h y)
  rw [← f.preimage_smoothLocus_fiberι (g y), ← b.preimage_smoothLocus_fiberι y] at H
  have hz := (congrArg (fun U ↦ z' ∈ U) H).to_iff
  change f.fiberι (g y) (Scheme.Hom.fiberMapOfIsPullback h y z') ∈ f.smoothLocus ↔
    b.fiberι y z' ∈ b.smoothLocus at hz
  rw [← Scheme.Hom.comp_apply, Scheme.Hom.fiberMapOfIsPullback_fiberι,
    Scheme.Hom.comp_apply] at hz
  simpa only [z', y, b, Scheme.Hom.fiberι_asFiber, Scheme.Hom.mem_preimage] using hz

end AlgebraicGeometry

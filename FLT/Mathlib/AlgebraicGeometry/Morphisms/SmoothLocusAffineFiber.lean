/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothLocusFiber
public import FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothLocusTransport

/-!
# Smooth loci on canonical fibres of affine morphisms

This gives the pointwise fibre criterion using `Scheme.Hom.fiberι` and
`Scheme.Hom.fiberToSpecResidueField`, rather than a separately chosen ring
residue field. The comparison also retains the map to the original scheme.
-/

public noncomputable section
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

private theorem inv_pullback_map_snd {X X' Y Z Z' : Scheme} (f : X ⟶ Z)
    (g : Y ⟶ Z) (f' : X' ⟶ Z') (g' : Y ⟶ Z')
    (a : X ⟶ X') (c : Z ⟶ Z') (h₁ : f ≫ c = a ≫ f')
    (h₂ : g ≫ c = 𝟙 Y ≫ g')
    [IsIso (pullback.map f g f' g' a (𝟙 Y) c h₁ h₂)] :
    inv (pullback.map f g f' g' a (𝟙 Y) c h₁ h₂) ≫ pullback.snd f g =
      pullback.snd f' g' := by
  apply (cancel_epi (pullback.map f g f' g' a (𝟙 Y) c h₁ h₂)).mp
  simp

/-- Canonical fibres of a finitely presented affine algebra are locally finitely presented. -/
instance Spec.fiberToSpecResidueField_lfp [Algebra.FinitePresentation R S]
    (p : PrimeSpectrum R) : LocallyOfFinitePresentation
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberToSpecResidueField p) :=
  inferInstanceAs (LocallyOfFinitePresentation (pullback.snd _ _))

set_option backward.isDefEq.respectTransparency false in
/-- The standard affine fibre comparison retains the inclusion into `Spec S`. -/
@[reassoc (attr := simp)]
theorem Spec.fiberToSpecResidueFieldIso_inv_fiberι (p : PrimeSpectrum R) :
    (Spec.fiberToSpecResidueFieldIso R S p).inv.left ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι p =
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) := by
  simp [Spec.fiberToSpecResidueFieldIso, Scheme.Hom.fiberι,
    Arrow.isoMk', Arrow.isoMk, inv_pullback_map_snd]

set_option backward.isDefEq.respectTransparency false in
/-- A flat finitely presented affine morphism has the same relative smooth
locus on its canonical fibre as that fibre has over its residue field. -/
theorem Spec.preimage_smoothLocus_fiberι [Algebra.FinitePresentation R S]
    [Module.Flat R S] (p : PrimeSpectrum R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι p ⁻¹ᵁ
      (Spec.map (CommRingCat.ofHom (algebraMap R S))).smoothLocus =
    ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberToSpecResidueField p).smoothLocus := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let e := Spec.fiberToSpecResidueFieldIso R S p
  ext x
  obtain ⟨q, rfl⟩ := e.inv.left.homeomorph.surjective x
  change f.fiberι p (e.inv.left q) ∈ f.smoothLocus ↔
    e.inv.left q ∈ (f.fiberToSpecResidueField p).smoothLocus
  change (e.inv.left ≫ f.fiberι p) q ∈ f.smoothLocus ↔ _
  have h := Spec.fiberToSpecResidueFieldIso_inv_fiberι (S := S) p
  change e.inv.left ≫ f.fiberι p = _ at h
  rw [h]
  change _ ↔ q ∈ e.inv.left ⁻¹ᵁ (f.fiberToSpecResidueField p).smoothLocus
  have he : e.inv.left ⁻¹ᵁ (f.fiberToSpecResidueField p).smoothLocus =
      (Spec.map (CommRingCat.ofHom
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)))).smoothLocus :=
    Scheme.Hom.preimage_smoothLocus_arrowIso _ _ e.symm
  exact (Spec.mem_smoothLocus_fiber_iff p.asIdeal q).trans
    (congrArg (fun U ↦ q ∈ U) he).to_iff.symm

end AlgebraicGeometry

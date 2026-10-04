/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothLocusSpec
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# Smooth loci and affine fibres

For a flat finitely presented algebra, the relative smooth locus commutes
with base change to each residue field. This statement uses the actual
categorical pullback, via the spectrum tensor-product comparison.
-/

public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The actual pullback to a residue field is the spectrum of the algebraic fibre. -/
def Spec.algebraicFiberIso (p : Ideal R) [p.IsPrime] :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField))) ≅
        Spec (.of (p.Fiber S)) :=
  pullbackSymmetry _ _ ≪≫ pullbackSpecIso R p.ResidueField S

/-- The comparison retains the projection to the original affine scheme. -/
@[reassoc (attr := simp)]
theorem Spec.algebraicFiberIso_inv_fst (p : Ideal R) [p.IsPrime] :
    (Spec.algebraicFiberIso (S := S) p).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) := by
  simp [Spec.algebraicFiberIso]

/-- The comparison retains the structure map to the residue field. -/
@[reassoc (attr := simp)]
theorem Spec.algebraicFiberIso_inv_snd (p : Ideal R) [p.IsPrime] :
    (Spec.algebraicFiberIso (S := S) p).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap p.ResidueField (p.Fiber S))) := by
  simp [Spec.algebraicFiberIso]

set_option backward.isDefEq.respectTransparency false in
/-- Relative smooth loci commute with the actual pullback of an affine flat
finitely presented morphism to an algebraic residue field. -/
theorem Spec.preimage_smoothLocus_residueField [Algebra.FinitePresentation R S]
    [Module.Flat R S] (p : Ideal R) [p.IsPrime] :
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField))) ⁻¹ᵁ
      (Spec.map (CommRingCat.ofHom (algebraMap R S))).smoothLocus =
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField)))).smoothLocus := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let g := Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField))
  let e := Spec.algebraicFiberIso (S := S) p
  ext x
  obtain ⟨q, rfl⟩ := e.inv.homeomorph.surjective x
  change (pullback.fst f g) (e.inv q) ∈ f.smoothLocus ↔
    e.inv q ∈ (pullback.snd f g).smoothLocus
  rw [← Scheme.Hom.comp_apply]
  have h₁ := Spec.algebraicFiberIso_inv_fst (S := S) p
  change e.inv ≫ pullback.fst f g = _ at h₁
  rw [h₁]
  change _ ↔ q ∈ e.inv ⁻¹ᵁ (pullback.snd f g).smoothLocus
  rw [Scheme.Hom.preimage_smoothLocus_eq]
  have h₂ := Spec.algebraicFiberIso_inv_snd (S := S) p
  change e.inv ≫ pullback.snd f g = _ at h₂
  rw! [h₂]
  exact Spec.mem_smoothLocus_fiber_iff p q

end AlgebraicGeometry

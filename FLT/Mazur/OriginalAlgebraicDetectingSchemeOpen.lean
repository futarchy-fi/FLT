/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalTranscendentalDetectingOpen
public import FLT.Mazur.OriginalTensorOrbitMorphisms

/-!
# Detecting opens tested by whole rational scheme morphisms

The coefficient condition is a nonempty original algebraic principal open.
Every rational scheme morphism into it, however selected, gives an original
point whose entire conjugacy orbit satisfies the unchanged extended opens.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace FLT.Mazur.TranscendentalCoefficientOrbitAvoidance
set_option backward.isDefEq.respectTransparency false
variable {k L K A : Type} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra L K] [Algebra k K] [IsScalarTower k L K]
  [Algebra.IsAlgebraic k L] [CommRing A] [Algebra k A] [IsDomain (L ⊗[k] A)]

omit [Algebra.IsAlgebraic k L] [IsDomain (L ⊗[k] A)] in
/-- A rational scheme morphism yields the actual scalar-linear map on tensor coordinates. -/
theorem rational_morphism_algebra (p : Spec (.of L) ⟶ Spec (.of (L ⊗[k] A)))
    (hp : p ≫ Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[k] A))) = 𝟙 _) :
    ∃ φ : L ⊗[k] A →ₐ[L] L, Spec.map (CommRingCat.ofHom φ.toRingHom) = p := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective p
  have h : φ.hom.comp (algebraMap L (L ⊗[k] A)) = RingHom.id L := by
    rw [← Spec.map_comp] at hp
    exact congrArg CommRingCat.Hom.hom
      (Spec.map_injective (hp.trans (Spec.map_id (CommRingCat.of L)).symm))
  exact ⟨{ φ.hom with commutes' := fun x ↦ RingHom.congr_fun h x }, rfl⟩

/-- The nonempty detecting open controls all whole rational maps, before any point selection. -/
theorem exists_detecting_scheme_open {J : Type*} [Finite J]
    (U : J → (Spec (.of (K ⊗[k] A))).Opens)
    (hU : ∀ j, (U j : Set (Spec (.of (K ⊗[k] A)))).Nonempty) :
    ∃ W : (Spec (.of (L ⊗[k] A))).Opens, (W : Set (Spec (.of (L ⊗[k] A)))).Nonempty ∧
      ∀ p : Spec (.of L) ⟶ Spec (.of (L ⊗[k] A)),
        p ≫ Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[k] A))) = 𝟙 _ →
        Set.range p ⊆ W →
        ∃ q : A →ₐ[k] L,
          p ≫ Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A).toRingHom) =
            originalPointMorphism q ∧
          ∀ (σ : L ≃ₐ[k] L) j, Set.range (originalExtendedMorphism (K := K) q σ) ⊆ U j := by
  obtain ⟨a, ha, hd⟩ := exists_original_detecting_condition (L := L) U hU
  refine ⟨PrimeSpectrum.basicOpen a, ?_, fun p hp hW ↦ ?_⟩
  · exact ⟨(⊥ : PrimeSpectrum (L ⊗[k] A)), ha⟩
  · obtain ⟨φ, rfl⟩ := rational_morphism_algebra p hp
    have hφ : φ a ≠ 0 := by
      have h := hW ⟨(⊥ : PrimeSpectrum L), rfl⟩
      exact h
    refine ⟨(φ.restrictScalars k).comp Algebra.TensorProduct.includeRight, ?_, ?_⟩
    · rw [← Spec.map_comp]
      rfl
    · intro σ j x hx
      obtain ⟨v, rfl⟩ := hx
      rw [originalExtendedMorphism_apply]
      exact hd φ hφ σ j

end FLT.Mazur.TranscendentalCoefficientOrbitAvoidance

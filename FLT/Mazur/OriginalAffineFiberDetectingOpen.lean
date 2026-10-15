/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalAlgebraicDetectingSchemeOpen
public import FLT.Mazur.OriginalAffineFiberOrbit

/-!
# Detecting opens in actual algebraic affine fibers

Transport the uniform detecting condition through both actual cartesian
squares. Every rational point of the resulting open controls its entire
larger-field orbit before a smooth étale point is selected.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
namespace FLT.Mazur.TranscendentalCoefficientOrbitAvoidance
set_option backward.isDefEq.respectTransparency false
variable {k L K A : Type} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra L K] [Algebra k K] [IsScalarTower k L K]
  [Algebra.IsAlgebraic k L] [CommRing A] [Algebra k A] [IsDomain (L ⊗[k] A)]
  {Y Z : Scheme}

/-- The actual algebraic fiber has an open controlling every conjugate in the actual K-fiber. -/
theorem exists_fiber_detecting_open
    (a : Y ⟶ Spec (.of K)) (b : Y ⟶ Spec (.of A))
    (H : IsPullback a b (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (Spec.map (CommRingCat.ofHom (algebraMap k A))))
    (c : Z ⟶ Spec (.of L)) (d : Z ⟶ Spec (.of A))
    (G : IsPullback c d (Spec.map (CommRingCat.ofHom (algebraMap k L)))
      (Spec.map (CommRingCat.ofHom (algebraMap k A))))
    {J : Type*} [Finite J] (U : J → Y.Opens)
    (hU : ∀ j, (U j : Set Y).Nonempty) :
    ∃ W : Z.Opens, (W : Set Z).Nonempty ∧
      ∀ p : Spec (.of L) ⟶ Z, p ≫ c = 𝟙 _ → Set.range p ⊆ W →
        ∃ z : (L ≃ₐ[k] L) → (Spec (.of K) ⟶ Y),
          (∀ σ, z σ ≫ a = 𝟙 _) ∧
          (∀ σ, z σ ≫ b = Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫
            Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ p ≫ d) ∧
          ∀ σ j, Set.range (z σ) ⊆ U j := by
  let e : Y ≅ Spec (.of (K ⊗[k] A)) := H.isoPullback ≪≫ pullbackSpecIso k K A
  let g : Z ≅ Spec (.of (L ⊗[k] A)) := G.isoPullback ≪≫ pullbackSpecIso k L A
  let U' (j : J) := e.inv ⁻¹ᵁ U j
  have hU' (j : J) : (U' j : Set (Spec (.of (K ⊗[k] A)))).Nonempty := by
    obtain ⟨y, hy⟩ := hU j
    refine ⟨e.hom y, ?_⟩
    change e.inv (e.hom y) ∈ U j
    rw [← Scheme.Hom.comp_apply, e.hom_inv_id]
    exact hy
  obtain ⟨W, hW, hd⟩ := exists_detecting_scheme_open (L := L) U' hU'
  refine ⟨g.hom ⁻¹ᵁ W, ?_, fun p hp hmem ↦ ?_⟩
  · obtain ⟨x, hx⟩ := hW
    refine ⟨g.inv x, ?_⟩
    change g.hom (g.inv x) ∈ W
    rw [← Scheme.Hom.comp_apply, g.inv_hom_id]
    exact hx
  · have hpc : (p ≫ g.hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[k] A))) = 𝟙 _ := by
      rw [Category.assoc]
      convert hp using 2
      simp only [g, Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_fst',
        IsPullback.isoPullback_hom_fst]
    have hpm : Set.range (p ≫ g.hom) ⊆ W := by
      rintro _ ⟨x, rfl⟩
      exact hmem ⟨x, rfl⟩
    obtain ⟨q, hq, hqU⟩ := hd (p ≫ g.hom) hpc hpm
    have hgd : g.inv ≫ d = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A).toRingHom) := by
      simp only [g, Iso.trans_inv, Category.assoc, IsPullback.isoPullback_inv_snd,
        pullbackSpecIso_inv_snd]
      rfl
    have hpd : p ≫ d = originalPointMorphism q := by
      rw [← hgd, Category.assoc, Iso.hom_inv_id_assoc] at hq
      exact hq
    refine ⟨fun σ ↦ originalExtendedMorphism (K := K) q σ ≫ e.inv, ?_, ?_, ?_⟩
    · intro σ
      simp only [e, Iso.trans_inv, Category.assoc, IsPullback.isoPullback_inv_fst,
        pullbackSpecIso_inv_fst']
      exact originalExtendedMorphism_base q σ
    · intro σ
      simp only [e, Iso.trans_inv, Category.assoc, IsPullback.isoPullback_inv_snd,
        pullbackSpecIso_inv_snd, hpd]
      exact originalExtendedMorphism_original q σ
    · intro σ j x hx
      obtain ⟨v, rfl⟩ := hx
      exact hqU σ j ⟨v, rfl⟩

end FLT.Mazur.TranscendentalCoefficientOrbitAvoidance

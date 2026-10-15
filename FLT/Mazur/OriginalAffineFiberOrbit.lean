/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalTensorOrbitMorphisms

/-!
# Algebraic point orbits in actual affine scheme fibers

Transport coefficient avoidance through an arbitrary cartesian square. The
result retains whole original algebraic points and unchanged larger-field opens.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
namespace FLT.Mazur.TranscendentalCoefficientOrbitAvoidance
set_option backward.isDefEq.respectTransparency false
variable {k L K A : Type} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra L K] [Algebra k K] [IsScalarTower k L K]
  [Algebra.IsAlgebraic k L] [IsAlgClosed L]
  [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsDomain (L ⊗[k] A)]
  {Y : Scheme} (a : Y ⟶ Spec (.of K)) (b : Y ⟶ Spec (.of A))
  (H : IsPullback a b (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (Spec.map (CommRingCat.ofHom (algebraMap k A))))

include H in
/-- A common whole original point has every conjugate in every actual extended open. -/
theorem exists_original_morphism_orbit_in_opens {J : Type*} [Finite J]
    (U : J → Y.Opens) (hU : ∀ j, (U j : Set Y).Nonempty) :
    ∃ (q : A →ₐ[k] L) (z : (L ≃ₐ[k] L) → (Spec (.of K) ⟶ Y)),
      (∀ σ, z σ ≫ a = 𝟙 _) ∧
      (∀ σ, z σ ≫ b = Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ originalPointMorphism q) ∧
      ∀ σ j, Set.range (z σ) ⊆ U j := by
  let e : Y ≅ Spec (.of (K ⊗[k] A)) := H.isoPullback ≪≫ pullbackSpecIso k K A
  let W (j : J) : TopologicalSpace.Opens (PrimeSpectrum (K ⊗[k] A)) :=
    ⟨e.inv ⁻¹' U j, (U j).isOpen.preimage e.inv.continuous⟩
  have hW (j : J) : (W j : Set (PrimeSpectrum (K ⊗[k] A))).Nonempty := by
    obtain ⟨y, hy⟩ := hU j
    refine ⟨e.hom y, ?_⟩
    change e.inv (e.hom y) ∈ U j
    rw [← Scheme.Hom.comp_apply, e.hom_inv_id]
    exact hy
  obtain ⟨q, hq⟩ := exists_original_point_orbit_in_opens (L := L) W hW
  refine ⟨q, fun σ ↦ originalExtendedMorphism (K := K) q σ ≫ e.inv, ?_, ?_, ?_⟩
  · intro σ
    simp only [e, Iso.trans_inv, Category.assoc, IsPullback.isoPullback_inv_fst,
      pullbackSpecIso_inv_fst']
    exact originalExtendedMorphism_base q σ
  · intro σ
    simp only [e, Iso.trans_inv, Category.assoc, IsPullback.isoPullback_inv_snd,
      pullbackSpecIso_inv_snd]
    exact originalExtendedMorphism_original q σ
  · intro σ j y hy
    obtain ⟨x, rfl⟩ := hy
    change e.inv (originalExtendedMorphism (K := K) q σ x) ∈ U j
    rw [originalExtendedMorphism_apply]
    exact hq σ j

end FLT.Mazur.TranscendentalCoefficientOrbitAvoidance

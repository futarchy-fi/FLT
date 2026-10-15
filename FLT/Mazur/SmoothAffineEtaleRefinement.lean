/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothFiberEtaleOpenPoint

/-!
# Étale refinements of smooth neighborhoods over affine bases

A smooth neighborhood meeting a geometric base test admits an affine étale
refinement meeting the same test. Its point in the smooth source may change;
all conditions holding on the whole smooth neighborhood remain available.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SmoothAffineEtaleRefinement
set_option backward.isDefEq.respectTransparency false
variable {R k K : Type} [CommRing R] [Field k] [Field K] [IsSepClosed K]
  {V : Scheme}

/-- Separable density constructs an étale refinement without prescribing its smooth coordinate. -/
theorem exists_lift_residue [Algebra k K] (f : V ⟶ Spec (.of R)) [Smooth f]
    (φ : R →+* k) (hφ : φ.SurjectiveOnStalks)
    (a : Spec (.of K) ⟶ V)
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ))) :
    ∃ (E : Scheme) (e : E ⟶ Spec (.of R)) (v : E ⟶ V) (z : Spec (.of K) ⟶ E),
      IsAffine E ∧ Etale e ∧ v ≫ f = e ∧
      z ≫ e = Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ)) := by
  let b := Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ))
  let w := pullback.lift a (𝟙 _) (by simpa only [Category.id_comp] using ha)
  have hn : Nonempty (pullback f b : Scheme) := ⟨w default⟩
  obtain ⟨E, e, v, z, _, hE, he, hv, hz, _, _⟩ :=
    SmoothFiberEtaleOpenPoint.exists_point f φ hφ (pullback.fst f b)
      (pullback.snd f b) (IsPullback.of_hasPullback f b) (𝟙 _) hn
  exact ⟨E, e, v, z, hE, he, hv, hz⟩

/-- Every smooth geometric lift over an affine spectrum has an actual affine étale refinement. -/
theorem exists_lift (f : V ⟶ Spec (.of R)) [Smooth f]
    (b : Spec (.of K) ⟶ Spec (.of R)) (a : Spec (.of K) ⟶ V) (ha : a ≫ f = b) :
    ∃ (E : Scheme) (e : E ⟶ Spec (.of R)) (v : E ⟶ V) (z : Spec (.of K) ⟶ E),
      IsAffine E ∧ Etale e ∧ v ≫ f = e ∧ z ≫ e = b := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective b
  let p := RingHom.ker ψ.hom
  let _ : p.IsPrime := RingHom.ker_isPrime ψ.hom
  have hu : p.primeCompl ≤ (IsUnit.submonoid K).comap ψ.hom := by
    intro r hr
    change IsUnit (ψ.hom r)
    exact isUnit_iff_ne_zero.mpr hr
  let θ := Ideal.ResidueField.lift p ψ.hom le_rfl hu
  let _ := θ.toAlgebra
  have he : (algebraMap p.ResidueField K).comp (algebraMap R p.ResidueField) = ψ.hom := by
    ext r
    exact Ideal.ResidueField.lift_algebraMap p ψ.hom le_rfl hu r
  have h := exists_lift_residue (K := K) f (algebraMap R p.ResidueField)
    p.surjectiveOnStalks_residueField a
  rw [he] at h
  exact h ha

/-- The construction retains an arbitrary affine original base, without replacing its points. -/
theorem exists_affine_lift {Y : Scheme} [IsAffine Y] (f : V ⟶ Y) [Smooth f]
    (b : Spec (.of K) ⟶ Y) (a : Spec (.of K) ⟶ V) (ha : a ≫ f = b) :
    ∃ (E : Scheme) (e : E ⟶ Y) (v : E ⟶ V) (z : Spec (.of K) ⟶ E),
      IsAffine E ∧ Etale e ∧ v ≫ f = e ∧ z ≫ e = b := by
  obtain ⟨E, e, v, z, hE, he, hv, hz⟩ :=
    exists_lift (f ≫ Y.isoSpec.hom) (b ≫ Y.isoSpec.hom) a (by rw [← Category.assoc, ha])
  refine ⟨E, e ≫ Y.isoSpec.inv, v, z, hE, inferInstance, ?_, ?_⟩
  · rw [← hv]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [← Category.assoc, hz, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.SmoothAffineEtaleRefinement

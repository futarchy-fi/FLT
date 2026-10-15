/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AlgebraicClosureEmbeddingConjugacy
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Conjugacy of independent whole geometric morphisms over a field

Two geometric morphisms with the same original image point are related by
a coefficient-preserving automorphism of the algebraic closure. Equality
is of scheme morphisms, retaining every residue-field embedding.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeometricResidueMorphismConjugacy
set_option backward.isDefEq.respectTransparency false
variable {k K : Type} [Field k] [Field K] [Algebra k K]
  [IsAlgClosed K] [Algebra.IsAlgebraic k K] {X : Scheme}

/-- Geometric morphisms above the same original point are conjugate as whole morphisms. -/
theorem exists_conjugacy (f : X ⟶ Spec (.of k))
    (p q : Spec (.of K) ⟶ X)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (hx : p default = q default) :
    ∃ σ : K ≃ₐ[k] K, Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ p = q := by
  obtain ⟨⟨x, u⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective p
  obtain ⟨⟨y, v⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective q
  change (Spec.map u ≫ X.fromSpecResidueField x) default =
    (Spec.map v ≫ X.fromSpecResidueField y) default at hx
  have hxy : x = y := by simpa only [Scheme.Hom.comp_apply,
    Scheme.fromSpecResidueField_apply] using hx
  subst y
  change Spec.map u ≫ X.fromSpecResidueField x ≫ f = _ at hp
  change Spec.map v ≫ X.fromSpecResidueField x ≫ f = _ at hq
  obtain ⟨α, hα⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ f)
  let _ : Algebra k (X.residueField x) := α.hom.toAlgebra
  have hu : u.hom.comp α.hom = algebraMap k K := by
    change (α ≫ u).hom = (CommRingCat.ofHom (algebraMap k K)).hom
    apply congrArg CommRingCat.Hom.hom
    apply Spec.map_injective
    simpa only [Spec.map_comp, hα] using hp
  have hv : v.hom.comp α.hom = algebraMap k K := by
    change (α ≫ v).hom = (CommRingCat.ofHom (algebraMap k K)).hom
    apply congrArg CommRingCat.Hom.hom
    apply Spec.map_injective
    simpa only [Spec.map_comp, hα] using hq
  let u' : X.residueField x →ₐ[k] K :=
    { u.hom with commutes' := fun r ↦ RingHom.congr_fun hu r }
  let v' : X.residueField x →ₐ[k] K :=
    { v.hom with commutes' := fun r ↦ RingHom.congr_fun hv r }
  obtain ⟨σ, hσ⟩ := AlgebraicClosureEmbeddingConjugacy.exists_conjugacy u' v'
  refine ⟨σ, ?_⟩
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
    (Spec.map u ≫ X.fromSpecResidueField x) = Spec.map v ≫ X.fromSpecResidueField x
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom hσ)

end FLT.Mazur.GeometricResidueMorphismConjugacy

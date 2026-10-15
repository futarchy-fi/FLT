/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AlgebraicEmbeddingTranscendentalFactor
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Whole residue morphisms over arbitrary larger fields

An L-point and an independent K-point with the same original support differ
by a k-automorphism of the algebraic closure L followed by L-to-K extension.
The residue algebraicity is derived from the L-point, with no restriction on K.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.TranscendentalResidueMorphismConjugacy
set_option backward.isDefEq.respectTransparency false
variable {k L K : Type} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra L K] [Algebra k K] [IsScalarTower k L K]
  [IsAlgClosed L] [Algebra.IsAlgebraic k L] {X : Scheme}

/-- Independent larger-field morphisms factor through closure conjugates at the same support. -/
theorem exists_conjugacy (f : X ⟶ Spec (.of k))
    (p : Spec (.of L) ⟶ X) (q : Spec (.of K) ⟶ X)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L)))
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (hx : p default = q default) :
    ∃ σ : L ≃ₐ[k] L, Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ p = q := by
  obtain ⟨⟨x, u⟩, rfl⟩ := (Scheme.SpecToEquivOfField L X).symm.surjective p
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
  have hu : u.hom.comp α.hom = algebraMap k L := by
    change (α ≫ u).hom = (CommRingCat.ofHom (algebraMap k L)).hom
    apply congrArg CommRingCat.Hom.hom
    apply Spec.map_injective
    simpa only [Spec.map_comp, hα] using hp
  have hv : v.hom.comp α.hom = algebraMap k K := by
    change (α ≫ v).hom = (CommRingCat.ofHom (algebraMap k K)).hom
    apply congrArg CommRingCat.Hom.hom
    apply Spec.map_injective
    simpa only [Spec.map_comp, hα] using hq
  let u' : X.residueField x →ₐ[k] L :=
    { u.hom with commutes' := fun r ↦ RingHom.congr_fun hu r }
  let v' : X.residueField x →ₐ[k] K :=
    { v.hom with commutes' := fun r ↦ RingHom.congr_fun hv r }
  let _ : Algebra.IsAlgebraic k (X.residueField x) :=
    Algebra.IsAlgebraic.of_injective u' u'.injective
  obtain ⟨σ, hσ⟩ := AlgebraicEmbeddingTranscendentalFactor.exists_conjugate_factor u' v'
  refine ⟨σ, ?_⟩
  change Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
    (Spec.map u ≫ X.fromSpecResidueField x) = Spec.map v ≫ X.fromSpecResidueField x
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom hσ)

end FLT.Mazur.TranscendentalResidueMorphismConjugacy

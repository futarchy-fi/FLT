/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesCover
public import FLT.Mazur.BaseAdicReesRestriction

/-!
# Restrictions of actual relative Rees charts

The tensor ring restrictions induce the original geometric inclusions on
the relative space. Their images are precisely the pulled-back subopens.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) {U V : X.affineOpens}

/-- Restriction on tensor coordinates commutes with the original chart projection. -/
lemma relativeRingRestriction_left (h : U.1 ≤ V.1) :
    let _ := chartAlgebra f V
    let _ := chartAlgebra f U
    (relativeRingRestriction f J h).toRingHom.comp
      (algebraMap Γ(X, V.1) (Γ(X, V.1) ⊗[R] reesAlgebra J)) =
    (algebraMap Γ(X, U.1) (Γ(X, U.1) ⊗[R] reesAlgebra J)).comp
      (X.presheaf.map (homOfLE h).op).hom := by
  let _ := chartAlgebra f V
  let _ := chartAlgebra f U
  ext r
  rfl

/-- The tensor restriction leaves the base Rees projection unchanged. -/
lemma relativeRingRestriction_right (h : U.1 ≤ V.1) :
    let _ := chartAlgebra f V
    let _ := chartAlgebra f U
    (relativeRingRestriction f J h).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := Γ(X, V.1))
        (B := reesAlgebra J)).toRingHom =
      (Algebra.TensorProduct.includeRight (R := R) (A := Γ(X, U.1))
        (B := reesAlgebra J)).toRingHom := by
  let _ := chartAlgebra f V
  let _ := chartAlgebra f U
  ext r
  change (chartRingRestriction f h) 1 ⊗ₜ[R] r = 1 ⊗ₜ[R] r
  rw [map_one]

/-- Tensor ring restriction is the actual geometric inclusion of relative charts. -/
@[reassoc]
lemma relativeRingRestriction_spec (h : U.1 ≤ V.1) :
    let _ := chartAlgebra f V
    let _ := chartAlgebra f U
    Spec.map (CommRingCat.ofHom (relativeRingRestriction f J h).toRingHom) ≫
      chartSpaceMap f J V = chartSpaceMap f J U := by
  let _ := chartAlgebra f V
  let _ := chartAlgebra f U
  apply pullback.hom_ext
  · have he :
        Spec.map (CommRingCat.ofHom (relativeRingRestriction f J h).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1)
            (Γ(X, V.1) ⊗[R] reesAlgebra J))) =
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1)
          (Γ(X, U.1) ⊗[R] reesAlgebra J))) ≫
          Spec.map (X.presheaf.map (homOfLE h).op) := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg (fun k ↦ Spec.map (CommRingCat.ofHom k))
        (relativeRingRestriction_left f J h)
    rw [Category.assoc, chartSpaceMap_fst, chartSpaceMap_fst,
      ← Category.assoc, he, Category.assoc]
    exact congrArg (fun k ↦ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1)
      (Γ(X, U.1) ⊗[R] reesAlgebra J))) ≫ k)
      (V.2.map_fromSpec U.2 (homOfLE h).op)
  · rw [Category.assoc, chartSpaceMap_snd, chartSpaceMap_snd, ← Spec.map_comp]
    exact congrArg (fun k ↦ Spec.map (CommRingCat.ofHom k))
      (relativeRingRestriction_right f J h)

/-- Restriction of tensor coordinates is an open immersion. -/
instance relativeRingRestriction_isOpenImmersion (h : U.1 ≤ V.1) :
    let _ := chartAlgebra f V
    let _ := chartAlgebra f U
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (relativeRingRestriction f J h).toRingHom)) := by
  let _ := chartAlgebra f V
  let _ := chartAlgebra f U
  let g := Spec.map (CommRingCat.ofHom (relativeRingRestriction f J h).toRingHom)
  have : IsOpenImmersion (g ≫ chartSpaceMap f J V) := by
    rw [relativeRingRestriction_spec]
    infer_instance
  exact IsOpenImmersion.of_comp g (chartSpaceMap f J V)

/-- Its image is exactly the portion of the larger chart above the smaller affine open. -/
lemma relativeRingRestriction_range (h : U.1 ≤ V.1) :
    let _ := chartAlgebra f V
    let _ := chartAlgebra f U
    Set.range (Spec.map (CommRingCat.ofHom (relativeRingRestriction f J h).toRingHom)) =
      chartSpaceMap f J V ⁻¹' (pullback.fst f (baseMap J) ⁻¹' U.1) := by
  let _ := chartAlgebra f V
  let _ := chartAlgebra f U
  rw [← chartSpaceMap_range f J U]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, (congrArg (fun k ↦ k x) (relativeRingRestriction_spec f J h)).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, (chartSpaceMap f J V).isOpenEmbedding.injective ?_⟩
    exact (congrArg (fun k ↦ k x) (relativeRingRestriction_spec f J h)).trans hx

/-- A principal subopen of a source chart pulls back to the same tensor-ring equation. -/
lemma chartSpaceMap_preimage_basicOpen (r : Γ(X, V.1)) :
    let _ := chartAlgebra f V
    chartSpaceMap f J V ⁻¹ᵁ (pullback.fst f (baseMap J) ⁻¹ᵁ X.basicOpen r) =
      PrimeSpectrum.basicOpen (algebraMap Γ(X, V.1)
        (Γ(X, V.1) ⊗[R] reesAlgebra J) r) := by
  let _ := chartAlgebra f V
  change (chartSpaceMap f J V ≫ pullback.fst f (baseMap J)) ⁻¹ᵁ X.basicOpen r = _
  rw [chartSpaceMap_fst]
  change Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1)
    (Γ(X, V.1) ⊗[R] reesAlgebra J))) ⁻¹ᵁ (V.2.fromSpec ⁻¹ᵁ X.basicOpen r) = _
  rw [V.2.fromSpec_preimage_basicOpen]
  rfl

end FLT.Mazur.BaseAdicRees

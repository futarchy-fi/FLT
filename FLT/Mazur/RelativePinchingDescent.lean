/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RingEqualizerDescent
public import FLT.Mazur.RelativePinchingLocalDescent
public import FLT.Mazur.PolygonNormalizationAlgebra
/-!
# Arbitrary-target pinching descent over commutative rings

Normalization maps identifying the specified endpoints descend uniquely to
the actual node and one-gon algebras, with no field assumption on the base.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
universe u
namespace FLT.Mazur.RelativePinchingDescent
open PolygonNodePresentation PolygonNodeEqualizer RelativePinchingLocalDescent
variable {R : Type u} [CommRing R]
/-- Unique one-gon descent to an arbitrary target scheme. -/
theorem oneGon_desc {Y : Scheme.{u}} (h : Spec (.of R[X]) ⟶ Y)
    (w : Spec.map (CommRingCat.ofHom (evalRingHom (0 : R))) ≫ h =
      Spec.map (CommRingCat.ofHom (evalRingHom (1 : R))) ≫ h) :
    ∃! d : Spec (.of (B (R := R))) ⟶ Y,
      Spec.map (CommRingCat.ofHom (B (R := R)).val.toRingHom) ≫ d = h := by
  apply RingEqualizerDescent.exists_desc (evalRingHom (0 : R)) (evalRingHom (1 : R)) h
  · exact PolygonNormalizationAlgebra.oneGon_inclusion_finite
  · intro r
    exact ⟨⟨C r, by simp⟩, by simp⟩
  · intro x
    obtain ⟨s, d, hs, hd⟩ := oneGon_exists_local_desc h w x
    exact ⟨oneGonDenominator s, d, hs, hd⟩

/-- Unique node descent from the product normalization. -/
theorem node_product_desc {Y : Scheme.{u}} (h : Spec (.of (R[X] × R[X])) ⟶ Y)
    (w : Spec.map (CommRingCat.ofHom (nodeFirst (R := R))) ≫ h =
      Spec.map (CommRingCat.ofHom nodeSecond) ≫ h) :
    ∃! d : Spec (.of (A (R := R))) ⟶ Y,
      Spec.map (CommRingCat.ofHom (inclusion (R := R)).toRingHom) ≫ d = h := by
  apply RingEqualizerDescent.exists_desc (nodeFirst (R := R)) nodeSecond h
  · exact PolygonNormalizationAlgebra.node_inclusion_finite
  · intro r
    exact ⟨⟨(C r, C r), by simp [nodeFirst, nodeSecond]⟩, by simp [nodeFirst]⟩
  · intro x
    obtain ⟨s, d, hs, hd⟩ := node_exists_local_desc h w x
    exact ⟨nodeDenominator s, d, hs, hd⟩
/-- Two branch maps agreeing along the origin descend uniquely. -/
theorem node_desc {Y : Scheme.{u}} (f g : Spec (.of R[X]) ⟶ Y)
    (w : Spec.map (CommRingCat.ofHom (evalRingHom (0 : R))) ≫ f =
      Spec.map (CommRingCat.ofHom (evalRingHom (0 : R))) ≫ g) :
    ∃! d : Spec (.of (A (R := R))) ⟶ Y,
      Spec.map (CommRingCat.ofHom (first (R := R)).toRingHom) ≫ d = f ∧
      Spec.map (CommRingCat.ofHom (second (R := R)).toRingHom) ≫ d = g := by
  let h := inv (coprodSpec R[X] R[X]) ≫ coprod.desc f g
  have h₁ : Spec.map (CommRingCat.ofHom (RingHom.fst R[X] R[X])) ≫ h = f := by
    rw [← coprodSpec_inl, Category.assoc]
    simp [h]
  have h₂ : Spec.map (CommRingCat.ofHom (RingHom.snd R[X] R[X])) ≫ h = g := by
    rw [← coprodSpec_inr, Category.assoc]
    simp [h]
  have hw : Spec.map (CommRingCat.ofHom (nodeFirst (R := R))) ≫ h =
      Spec.map (CommRingCat.ofHom nodeSecond) ≫ h := by
    rw [nodeFirst, nodeSecond, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp,
      Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, h₁, h₂]
    exact w
  let ν := Spec.map (CommRingCat.ofHom (inclusion (R := R)).toRingHom)
  have hb₁ : Spec.map (CommRingCat.ofHom (RingHom.fst R[X] R[X])) ≫ ν =
      Spec.map (CommRingCat.ofHom (first (R := R)).toRingHom) := by
    rw [← Spec.map_comp]; rfl
  have hb₂ : Spec.map (CommRingCat.ofHom (RingHom.snd R[X] R[X])) ≫ ν =
      Spec.map (CommRingCat.ofHom (second (R := R)).toRingHom) := by
    rw [← Spec.map_comp]; rfl
  obtain ⟨d, hd, hu⟩ := node_product_desc h hw
  have hd' : ν ≫ d = h := hd
  refine ⟨d, ⟨?_, ?_⟩, ?_⟩
  · rw [← hb₁, Category.assoc, hd', h₁]
  · rw [← hb₂, Category.assoc, hd', h₂]
  · rintro e ⟨he₁, he₂⟩
    apply hu e
    change ν ≫ e = h
    apply (cancel_epi (coprodSpec R[X] R[X])).mp
    apply coprod.hom_ext
    · rw [coprodSpec_inl_assoc, coprodSpec_inl_assoc, ← Category.assoc, hb₁, he₁, h₁]
    · rw [coprodSpec_inr_assoc, coprodSpec_inr_assoc, ← Category.assoc, hb₂, he₂, h₂]
end FLT.Mazur.RelativePinchingDescent

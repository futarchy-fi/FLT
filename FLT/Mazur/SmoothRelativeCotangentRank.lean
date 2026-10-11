/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineStructuralSmoothLocus
public import FLT.Mazur.SmoothCotangentRankGenerization

/-!
# Cotangent ranks on every affine chart of a relative smooth scheme

Local standard-smooth presentations compute the cotangent rank of every
original affine prime, without requiring the entire affine chart to have a
single standard-smooth presentation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.SmoothRelativeCotangentRank

set_option backward.isDefEq.respectTransparency false

/-- Local standard-smooth relative dimension determines every original residue cotangent rank. -/
theorem finrank_eq (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (d : ℕ)
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d) (algebraMap R A))
    (p : Ideal A) [p.IsPrime] :
    Module.finrank p.ResidueField (p.ResidueField ⊗[A] Ω[A⁄R]) = d := by
  obtain ⟨s, hs, hstd⟩ := h
  have hex : ∃ f ∈ s, f ∉ p := by
    by_contra! he
    have hp : Ideal.span s ≤ p := Ideal.span_le.mpr he
    rw [hs] at hp
    exact (inferInstance : p.IsPrime).ne_top (top_le_iff.mp hp)
  obtain ⟨f, hf, hfp⟩ := hex
  have hd := hstd f hf
  rw [← IsScalarTower.algebraMap_eq R A (Localization.Away f),
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at hd
  let _ := hd
  exact SmoothCotangentRankGenerization.finrank_eq_of_away R A f d p hfp

/-- Every affine chart of a smooth relative-dimension-d scheme has cotangent rank d. -/
theorem affine_finrank_eq {R : Type} [CommRing R] {X : Scheme}
    (f : X ⟶ Spec (.of R)) (d : ℕ) [SmoothOfRelativeDimension d f]
    (U : X.affineOpens) (p : Ideal Γ(X, U)) [p.IsPrime] :
    let _ := (AffineStructuralSmoothLocus.scalars f U).toAlgebra
    Module.finrank p.ResidueField (p.ResidueField ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R]) = d := by
  let _ := (AffineStructuralSmoothLocus.scalars f U).toAlgebra
  have hs : SmoothOfRelativeDimension d (U.2.fromSpec ≫ f) :=
    IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension d) inferInstance U.2.fromSpec
  rw [AffineStructuralSmoothLocus.fromSpec_toBase,
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)] at hs
  exact finrank_eq R Γ(X, U) d hs p

end FLT.Mazur.SmoothRelativeCotangentRank

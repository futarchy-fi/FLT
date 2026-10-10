/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.QuasicoherentImageIdeal
public import FLT.Mazur.LineTrivializationCoordinates

/-!
# Cartier regularity of an embedded line

The full image ideal of an injective line-sheaf map to the structure sheaf
is effective Cartier. On a trivializing chart its equation is the image of
the actual basis section; injectivity proves that equation is regular.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

/-- A map from a free rank-one module has the principal ideal of its basis image. -/
lemma linearImage_eq_span_basis {R P : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    (a : P →ₗ[R] R) (e : P ≃ₗ[R] R) :
    a.range = Ideal.span {a (e.symm 1)} := by
  ext r
  constructor
  · rintro ⟨s, rfl⟩
    have hs : s = e s • e.symm 1 := by
      apply e.injective
      simp
    rw [hs, a.map_smul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
  · intro hr
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hr
    refine ⟨t • e.symm 1, ?_⟩
    simpa only [a.map_smul, smul_eq_mul, mul_comm] using ht.symm

/-- An injective map from a rank-one free module has a regular basis image. -/
lemma linearImage_basis_regular {R P : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    (a : P →ₗ[R] R) (e : P ≃ₗ[R] R) (ha : Function.Injective a) :
    IsRegular (a (e.symm 1)) := by
  rw [← isRightRegular_iff_isRegular]
  intro r t h
  have he : r • e.symm 1 = t • e.symm 1 := ha (by
    simpa only [a.map_smul, smul_eq_mul] using h)
  simpa using congrArg e he

variable {X : Scheme} {M : X.Modules} [M.IsQuasicoherent]
  (a : M ⟶ structureModule X)

omit [M.IsQuasicoherent] in
/-- Coordinates identify the image on a trivializing affine chart, without radicals. -/
lemma affineImageIdeal_eq_span (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ structureModule U.1.toScheme) :
    affineImageIdeal a U = Ideal.span (α := Γ(X, U))
      {(a.val.app (op U.1)).hom ((lineTrivializationCoordinates e le_rfl).symm 1)} :=
  linearImage_eq_span_basis (R := Γ(X, U)) (a.val.app (op U.1)).hom
    (lineTrivializationCoordinates e le_rfl)

/-- Every trivializing affine neighborhood is an actual Cartier chart. -/
lemma image_cartierChart [Mono a] (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ structureModule U.1.toScheme) :
    CartierChart (quasicoherentImageIdeal a) U := by
  refine ⟨a.app U.1 ((lineTrivializationCoordinates e le_rfl).symm 1), ?_,
    affineImageIdeal_eq_span a U e⟩
  have : Mono a.val :=
    inferInstanceAs (Mono ((SheafOfModules.forget _).map a))
  exact linearImage_basis_regular (R := Γ(X, U)) (a.val.app (op U.1)).hom
    (lineTrivializationCoordinates e le_rfl)
    (PresheafOfModules.injective_of_mono a.val (op U.1))

/-- The full image ideal of an embedded line is effective Cartier on any scheme. -/
theorem image_effectiveCartier [Mono a] (hM : LocallyFreeRankOne M) :
    EffectiveCartier (quasicoherentImageIdeal a) := by
  intro x
  obtain ⟨U, hx, hU, ⟨e⟩⟩ := hM.exists_affine_trivialization x
  exact ⟨⟨U, hU⟩, hx, image_cartierChart a ⟨U, hU⟩ e⟩

end FLT.Mazur.FCurve

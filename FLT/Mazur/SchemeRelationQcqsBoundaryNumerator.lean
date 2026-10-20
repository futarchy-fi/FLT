/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineNormGluingFiber
public import FLT.Mazur.SchemeRelationPrincipalLocalization
public import FLT.Mazur.SchemeInvariantPrincipalBoundaryNumerator
public import FLT.Mazur.InvariantOpenCoefficientGluing

/-!
# Exact full relation boundary numerators on nonaffine qcqs sources

Both the source and boundary may be nonaffine. Compactness and quasi-separatedness
clear the full relation and boundary equations. This provides global scalar
multiples of local boundary lifts without asserting that a geometric principal
cover generates the unit ideal in global functions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeRelationQcqsBoundaryNumerator
open SchemeEffectiveEpiSections InvariantOpenCoefficientRestriction
open SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
variable {D X Y : Scheme.{0}} (p q : D ⟶ X) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace D] [QuasiSeparatedSpace D] (r : compatibleFunctions p q)
local notation "U" => X.basicOpen r.val
local notation "hU" => compatibleFunctions_basicOpen p q r

/-- The full restricted relation has an actual original invariant numerator. -/
theorem exists_numerator (v : coefficients p q U hU) :
    ∃ (n : ℕ) (w : compatibleFunctions p q),
      (U).ι.appTop w.val = ((U).ι.appTop r.val) ^ n * v.val := by
  let z := (relationOpenCoordinates p q U hU).symm v
  obtain ⟨w, n, hw⟩ :=
    SchemeRelationPrincipalLocalization.exists_invariant_numerator p q r z
  refine ⟨n, w, ?_⟩
  have hz : (U).topIso.inv z.val = v.val :=
    congrArg Subtype.val ((relationOpenCoordinates p q U hU).apply_symm_apply v)
  have ht (a : Γ(X, ⊤)) :
      (U).topIso.inv (algebraMap Γ(X, ⊤) Γ(X, U) a) = (U).ι.appTop a :=
    AffineNormGluing.topIso_inv_global (U) a
  have hh := congrArg (U).topIso.inv hw
  rw [map_mul, hz, ht, ht, map_pow, mul_comm] at hh
  exact hh.symm

variable (i : Y ⟶ X) [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- Clear both relation and boundary denominators on the unchanged qcqs schemes. -/
theorem exists_boundary_numerator (v : coefficients p q U hU) (t : Γ(Y, ⊤))
    (hv : (principalPullbackMap i r.val).appTop v.val =
      (Y.basicOpen (i.appTop r.val)).ι.appTop t) :
    ∃ (n : ℕ) (w : compatibleFunctions p q),
      i.appTop w.val = (i.appTop r.val) ^ n * t ∧
      (U).ι.appTop w.val = ((U).ι.appTop r.val) ^ n * v.val := by
  obtain ⟨n, w, hw⟩ := exists_numerator p q r v
  have hb : (Y.basicOpen (i.appTop r.val)).ι.appTop (i.appTop w.val) =
      (Y.basicOpen (i.appTop r.val)).ι.appTop ((i.appTop r.val) ^ n * t) := by
    rw [← principalPullbackMap_appTop, hw]
    simp only [map_mul, map_pow, hv, principalPullbackMap_appTop]
  have hb' := congrArg (Y.basicOpen (i.appTop r.val)).topIso.hom hb
  simp only [InvariantOpenCoefficientGluing.inclusion_coordinates] at hb'
  let _ : IsLocalization.Away (i.appTop r.val) Γ(Y, Y.basicOpen (i.appTop r.val)) :=
    isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ _
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq (i.appTop r.val) hb'
  refine ⟨k + n, r ^ k * w, ?_, ?_⟩
  · change i.appTop (r.val ^ k * w.val) = _
    rw [map_mul, map_pow, hk, pow_add, mul_assoc]
  · change (U).ι.appTop (r.val ^ k * w.val) = _
    simp only [map_mul, map_pow, hw, pow_add, mul_assoc]

/-- A homogeneous principal correction extends to an exact original boundary-zero numerator. -/
theorem exists_kernel_numerator (v : coefficients p q U hU)
    (hv : (principalPullbackMap i r.val).appTop v.val = 0) :
    ∃ (n : ℕ) (w : compatibleFunctions p q), i.appTop w.val = 0 ∧
      (U).ι.appTop w.val = ((U).ι.appTop r.val) ^ n * v.val := by
  obtain ⟨n, w, hw, he⟩ := exists_boundary_numerator p q r i v 0
    (by simpa only [map_zero] using hv)
  exact ⟨n, w, by simpa only [mul_zero] using hw, he⟩

end FLT.Mazur.SchemeRelationQcqsBoundaryNumerator

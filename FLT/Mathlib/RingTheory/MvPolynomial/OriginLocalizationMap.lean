/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PolynomialLocalDimension
public import FLT.Mathlib.RingTheory.MvPolynomial.FiniteFieldDescent
public import Mathlib.RingTheory.RingHom.Flat

/-! # Coefficient extension between polynomial local rings at the origin -/

@[expose] public noncomputable section

namespace MvPolynomial

variable (k K : Type*) [Field k] [Field K] [Algebra k K] (n : ℕ)

/-- The polynomial ring localized at its rational origin. -/
abbrev OriginLocalization :=
  Localization.AtPrime (rationalPointIdeal (fun _ : Fin n ↦ (0 : k)))

/-- Coefficient extension pulls the origin ideal back to the origin ideal. -/
theorem originIdeal_comap_map :
    rationalPointIdeal (fun _ : Fin n ↦ (0 : k)) =
      (rationalPointIdeal (fun _ : Fin n ↦ (0 : K))).comap (map (algebraMap k K)) := by
  ext f
  change aeval (fun _ ↦ (0 : k)) f = 0 ↔
    aeval (fun _ ↦ (0 : K)) (map (algebraMap k K) f) = 0
  simp only [aeval_zero', Algebra.algebraMap_self, RingHom.id_apply,
    constantCoeff_map, map_eq_zero]

/-- Extend coefficients in a fraction, keeping its polynomial coordinates. -/
def originLocalizationMap : OriginLocalization k n →+* OriginLocalization K n :=
  Localization.localRingHom _ _ (map (algebraMap k K)) (originIdeal_comap_map k K n)

@[simp] theorem originLocalizationMap_algebraMap (f : MvPolynomial (Fin n) k) :
    originLocalizationMap k K n (algebraMap _ (OriginLocalization k n) f) =
      algebraMap _ (OriginLocalization K n) (map (algebraMap k K) f) :=
  Localization.localRingHom_to_map _ _ _ _ f

instance originLocalizationMap_isLocalHom : IsLocalHom (originLocalizationMap k K n) :=
  Localization.isLocalHom_localRingHom _ _ _ _

/-- Flatness of coefficient extension survives localization at the origin. -/
theorem originLocalizationMap_flat : (originLocalizationMap k K n).Flat := by
  let := algebraMvPolynomial (σ := Fin n) (R := k) (S := K)
  let e := Algebra.IsPushout.equiv k (MvPolynomial (Fin n) k) K
    (MvPolynomial (Fin n) K)
  have : Module.Flat (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) :=
    Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  have hf : (map (σ := Fin n) (algebraMap k K)).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  exact hf.localRingHom _ _ _

/-- Local polynomial coefficient extension preserves and reflects regular lists. -/
theorem isRegular_originLocalizationMap_iff (rs : List (OriginLocalization k n)) :
    RingTheory.Sequence.IsRegular (OriginLocalization K n)
        (rs.map (originLocalizationMap k K n)) ↔
      RingTheory.Sequence.IsRegular (OriginLocalization k n) rs := by
  let := (originLocalizationMap k K n).toAlgebra
  have : IsLocalHom (algebraMap (OriginLocalization k n) (OriginLocalization K n)) :=
    originLocalizationMap_isLocalHom k K n
  have : Module.Flat (OriginLocalization k n) (OriginLocalization K n) :=
    originLocalizationMap_flat k K n
  have : Module.FaithfullyFlat (OriginLocalization k n) (OriginLocalization K n) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact RingTheory.Sequence.isRegular_iff_of_faithfullyFlat

end MvPolynomial

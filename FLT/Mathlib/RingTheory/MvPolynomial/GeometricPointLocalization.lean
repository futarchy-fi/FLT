/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.OriginLocalizationMap

/-! # Local coefficient extension at arbitrary geometric points -/

@[expose] public noncomputable section

namespace MvPolynomial

variable (k K : Type*) [Field k] [Field K] [Algebra k K] {n : ℕ} (a : Fin n → K)

/-- The original local ring at the contraction of a geometric point.
Its residue field need not equal the original coefficient field. -/
abbrev GeometricPointSource :=
  Localization.AtPrime ((rationalPointIdeal a).comap (map (algebraMap k K)))

/-- Coefficient extension localized at a geometric point and its contraction. -/
def geometricPointLocalizationMap :
    GeometricPointSource k K a →+* Localization.AtPrime (rationalPointIdeal a) :=
  Localization.localRingHom _ _ (map (algebraMap k K)) rfl

@[simp] theorem geometricPointLocalizationMap_algebraMap (f : MvPolynomial (Fin n) k) :
    geometricPointLocalizationMap k K a (algebraMap _ (GeometricPointSource k K a) f) =
      algebraMap _ (Localization.AtPrime (rationalPointIdeal a)) (map (algebraMap k K) f) :=
  Localization.localRingHom_to_map _ _ _ _ f

instance geometricPointLocalizationMap_isLocalHom :
    IsLocalHom (geometricPointLocalizationMap k K a) :=
  Localization.isLocalHom_localRingHom _ _ _ _

/-- Flatness holds at every geometric point, including points with non-rational contraction. -/
theorem geometricPointLocalizationMap_flat : (geometricPointLocalizationMap k K a).Flat := by
  let := algebraMvPolynomial (σ := Fin n) (R := k) (S := K)
  let e := Algebra.IsPushout.equiv k (MvPolynomial (Fin n) k) K (MvPolynomial (Fin n) K)
  have : Module.Flat (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) :=
    Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  have hf : (map (σ := Fin n) (algebraMap k K)).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  exact hf.localRingHom _ _ _

/-- Localizing first or extending coefficients first gives the same extended ideal. -/
theorem map_ideal_geometricPointLocalization (I : Ideal (MvPolynomial (Fin n) k)) :
    (I.map (algebraMap _ (GeometricPointSource k K a))).map
        (geometricPointLocalizationMap k K a) =
      (I.map (map (algebraMap k K))).map
        (algebraMap _ (Localization.AtPrime (rationalPointIdeal a))) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro f
  exact geometricPointLocalizationMap_algebraMap k K a f

end MvPolynomial

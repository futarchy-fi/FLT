/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.GeometricRegularDescent

/-! # Reflect regularity of a specified square parameter list -/

@[expose] public noncomputable section

namespace MvPolynomial

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {n : ℕ}

/-- A specified square list is regular if its geometric quotient is nonzero Artinian.
Faithful flatness reflects the regularity of this list without changing generators. -/
theorem isRegular_parameters_at_geometricPoint (a : Fin n → K)
    (rs : List (GeometricPointSource k K a)) (hlen : rs.length = n)
    [IsArtinianRing (Localization.AtPrime (rationalPointIdeal a) ⧸
      Ideal.ofList (rs.map (geometricPointLocalizationMap k K a)))]
    [Nontrivial (Localization.AtPrime (rationalPointIdeal a) ⧸
      Ideal.ofList (rs.map (geometricPointLocalizationMap k K a)))] :
    RingTheory.Sequence.IsRegular (GeometricPointSource k K a) rs := by
  let S := Localization.AtPrime (rationalPointIdeal a)
  let := (geometricPointLocalizationMap k K a).toAlgebra
  have : IsLocalHom (algebraMap (GeometricPointSource k K a) S) :=
    geometricPointLocalizationMap_isLocalHom k K a
  have : Module.Flat (GeometricPointSource k K a) S :=
    geometricPointLocalizationMap_flat k K a
  have : Module.FaithfullyFlat (GeometricPointSource k K a) S :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  apply (RingTheory.Sequence.isRegular_iff_of_faithfullyFlat (S := S)).mp
  exact isRegular_parameters_at_rationalPoint a _ (by simpa using hlen)

end MvPolynomial

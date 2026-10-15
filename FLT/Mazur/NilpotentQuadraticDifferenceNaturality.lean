/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NilpotentQuadraticDifferenceFactors
public import FLT.Mazur.WeierstrassDilatationTangentRootNaturality

/-!
# The actual quadratic factors commute with coefficient restriction

Uniqueness preserves the chosen polynomial root. Both full factors then
agree after replacing the source coefficients by their target images.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.NilpotentQuadraticDifference
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (K : R[X]) (I : Ideal R) (hI : IsNilpotent I) (J : Ideal S) (hJ : IsNilpotent J)
  (hf : I ≤ J.comap f) (hK : K ∈ I.map C)
local notation "hKJ" => WeierstrassDilatation.terminalPolynomialIdeal_map f I J hf hK

/-- The actual small polynomial factor root commutes with coefficient restriction. -/
theorem factorRoot_map :
    (factorRoot K I hI hK).map f = factorRoot (K.map f) J hJ hKJ := by
  have h := NilpotentQuadraticRoot.root_map (I.map C)
    (NilpotentPolynomialInverse.mapIdeal_nilpotent I hI C) (J.map C)
    (NilpotentPolynomialInverse.mapIdeal_nilpotent J hJ C) (-1) K isUnit_one.neg hK
    (Polynomial.mapRingHom f) (WeierstrassDilatation.terminalPolynomialIdeal_map f I J hf)
  simpa only [factorRoot, Polynomial.coe_mapRingHom, Polynomial.map_neg, Polynomial.map_one] using h

/-- The full first factor agrees with the construction from the restricted coefficients. -/
theorem smallFactor_coefficients (u v : S) :
    smallFactor K I hI hK f u v =
      smallFactor (K.map f) J hJ hKJ (RingHom.id S) u v := by
  simp only [smallFactor]
  rw [← factorRoot_map f K I hI J hJ hf hK]
  rw [eval₂_id, eval_map]

/-- The full opposite factor agrees with the construction from the restricted coefficients. -/
theorem oppositeFactor_coefficients (u v : S) :
    oppositeFactor K I hI hK f u v =
      oppositeFactor (K.map f) J hJ hKJ (RingHom.id S) u v := by
  simp only [oppositeFactor]
  rw [← factorRoot_map f K I hI J hJ hf hK]
  rw [eval₂_id, eval_map]

end FLT.Mazur.NilpotentQuadraticDifference

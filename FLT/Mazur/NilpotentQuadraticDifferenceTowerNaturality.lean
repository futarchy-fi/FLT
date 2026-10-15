/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NilpotentQuadraticDifferenceNaturality

/-!
# Full quadratic factors after a further coefficient extension

The factors constructed over two nilpotent coefficient rings agree in every
algebra over the target. This retains the entire polynomial correction.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.NilpotentQuadraticDifference
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  (f : R →+* S) (g : S →+* T)
  (K : R[X]) (I : Ideal R) (hI : IsNilpotent I) (J : Ideal S) (hJ : IsNilpotent J)
  (hf : I ≤ J.comap f) (hK : K ∈ I.map C) (u v : T)
local notation "hKJ" => WeierstrassDilatation.terminalPolynomialIdeal_map f I J hf hK

/-- The full first factor is compatible with both stages of a coefficient tower. -/
theorem smallFactor_tower :
    smallFactor K I hI hK (g.comp f) u v =
      smallFactor (K.map f) J hJ hKJ g u v := by
  simp only [smallFactor]
  rw [← factorRoot_map f K I hI J hJ hf hK, Polynomial.eval₂_map]

/-- The full opposite factor is compatible with both stages of a coefficient tower. -/
theorem oppositeFactor_tower :
    oppositeFactor K I hI hK (g.comp f) u v =
      oppositeFactor (K.map f) J hJ hKJ g u v := by
  simp only [oppositeFactor]
  rw [← factorRoot_map f K I hI J hJ hf hK, Polynomial.eval₂_map]

end FLT.Mazur.NilpotentQuadraticDifference

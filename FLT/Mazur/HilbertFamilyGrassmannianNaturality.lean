/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianScalarExtension
public import FLT.Mazur.HilbertFamilyGrassmannianParameter
public import FLT.Mazur.HilbertFamilyRelationBaseChange
public import FLT.Mazur.HilbertPolynomialFamilyBaseChangeRank

/-!
# Naturality of the finite flat Hilbert Grassmannian parameter

The parameter of the actual extended ideal equals scalar extension of the
original parameter in the canonical bounded polynomial coordinates. All new
finite-presentation, flatness and rank hypotheses are constructed from the
original family; the coefficient algebra is arbitrary.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.HilbertChart
universe u
variable (S T I : Type u) [CommRing S] [CommRing T] [Algebra S T]
  (J : Ideal (MvPolynomial I S)) (d : ℕ)
  [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
  [Module.Flat S (MvPolynomial I S ⧸ J)]
  (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
    (MvPolynomial I p.asIdeal.ResidueField ⧸
      J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)

/-- The actual extended family supplies its own Grassmannian parameter. -/
def extendedFamilyGrassmannianParameter :
    Module.Grassmannian T (MvPolynomial.restrictTotalDegree I T (d + 1)) d := by
  let _ := polynomialQuotient_finitePresentation_baseChange I S J T
  let _ := polynomialQuotient_flat_baseChange I S J T
  exact finiteFlatGrassmannianParameter T I (J.map (MvPolynomial.map (algebraMap S T))) d
    (polynomialQuotient_residueRank_baseChange I S J T d hd)

/-- The extended parameter contains exactly the extended ideal's bounded relations. -/
theorem extendedFamilyGrassmannianParameter_submodule :
    (extendedFamilyGrassmannianParameter S T I J d hd).toSubmodule =
      boundedRelationKernel T I (J.map (MvPolynomial.map (algebraMap S T))) (d + 1) := rfl

/-- Hilbert Grassmannian parameters commute with every coefficient extension. -/
theorem finiteFlatGrassmannianParameter_natural :
    grassmannianScalarExtension T (finiteFlatGrassmannianParameter S I J d hd)
        (boundedPolynomialBaseChangeEquiv S T I (d + 1)) =
      extendedFamilyGrassmannianParameter S T I J d hd := by
  apply Module.Grassmannian.ext
  rw [grassmannianScalarExtension_submodule, finiteFlatGrassmannianParameter_submodule,
    extendedFamilyGrassmannianParameter_submodule]
  exact boundedRelationKernel_baseChange_map S T I J d (d + 1) hd (Nat.le_succ d)

end FLT.Mazur.HilbertChart

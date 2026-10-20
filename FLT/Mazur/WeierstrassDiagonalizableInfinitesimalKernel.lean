/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DiagonalizableCoefficientReduction
public import FLT.Mazur.WeierstrassSmoothSurjectiveKernel

/-!
# Character coordinates on the actual smooth-group reduction kernel

For a Weierstrass curve over an arbitrary base, including a singular arithmetic
one-gon, smooth-group points on a diagonalizable test scheme have an explicit
square-zero reduction kernel. Its coordinates are ideal-valued characters.
Taking the character group to be Z/n gives the nonetale roots-of-unity tests
needed for subgroup lifting, without requiring n to be invertible.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.WeierstrassDiagonalizableInfinitesimalKernel

open DiagonalizableCobar WeierstrassIntegralChart

universe u
variable {R G : Type u} [CommRing R] [AddCommMonoid G]
  (W : WeierstrassCurve R) (I : Ideal R) (hI : I ^ 2 = ⊥)

/-- The exact kernel of reduction to the original quotient coefficient ring. -/
def kernelEquiv : Multiplicative (G →₀ I) ≃*
    (smoothAlgebraReduction W (coefficientReduction R G I)).ker :=
  ((AddEquiv.toMultiplicative (idealCoefficientsEquiv R G I).toAddEquiv).trans
    (smoothSquareZeroKernelEquiv W (coefficientIdeal R G I)
      (coefficientIdeal_sq_zero R G I hI))).trans
    (MulEquiv.subgroupCongr
      (smoothAlgebraReduction_ker W (coefficientReduction R G I)
        (coefficientReduction_surjective R G I)).symm)

/-- The kernel comparison is the original infinitesimal Weierstrass point. -/
theorem kernelEquiv_point (q : G →₀ I) :
    (kernelEquiv (G := G) W I hI (Multiplicative.ofAdd q)).val =
      smoothInfinitesimalPoint W (coefficientIdeal R G I)
        (coefficientIdeal_sq_zero R G I hI) (fromIdealCoefficients R G I q) := rfl

/-- Every original smooth-group error reducing to the identity has these full coordinates. -/
theorem existsUnique_coefficients
    (p : (smoothAlgebraReduction W (coefficientReduction R G I)).ker) :
    ∃! q : G →₀ I, (kernelEquiv (G := G) W I hI (Multiplicative.ofAdd q)).val = p.val := by
  refine ⟨((kernelEquiv W I hI).symm p).toAdd, ?_, ?_⟩
  · exact congrArg Subtype.val ((kernelEquiv W I hI).apply_symm_apply p)
  · intro q hq
    have h : kernelEquiv W I hI (Multiplicative.ofAdd q) = p := Subtype.ext hq
    exact congrArg Multiplicative.toAdd ((kernelEquiv W I hI).injective
      (h.trans ((kernelEquiv W I hI).apply_symm_apply p).symm))

/-- Addition of all character coefficients is the actual original smooth-group product. -/
theorem kernelEquiv_add (p q : G →₀ I) :
    (kernelEquiv (G := G) W I hI (Multiplicative.ofAdd (p + q))).val =
      (kernelEquiv W I hI (Multiplicative.ofAdd p)).val *
        (kernelEquiv W I hI (Multiplicative.ofAdd q)).val :=
  congrArg Subtype.val ((kernelEquiv W I hI).map_mul
    (Multiplicative.ofAdd p) (Multiplicative.ofAdd q))

/-- The full inserted correction has exactly identity reduction on the specified base fiber. -/
theorem kernelEquiv_reduction (q : G →₀ I) :
    smoothAlgebraReduction W (coefficientReduction R G I)
      (kernelEquiv (G := G) W I hI (Multiplicative.ofAdd q)).val = 1 :=
  (kernelEquiv W I hI (Multiplicative.ofAdd q)).property

end FLT.Mazur.WeierstrassDiagonalizableInfinitesimalKernel

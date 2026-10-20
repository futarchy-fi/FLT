/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DiagonalizableInfinitesimalNaturality
public import FLT.Mazur.WeierstrassDiagonalizableInfinitesimalKernel
public import FLT.Mazur.WeierstrassSmoothInfinitesimalNaturality

/-!
# Character cofaces on the actual Weierstrass kernel

The full ideal-valued character coordinates are natural under all character
substitutions. In particular every coface used by the integral cocycle
contraction is the restriction of the original smooth-group point.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.WeierstrassDiagonalizableInfinitesimalKernel

open DiagonalizableCobar WeierstrassIntegralChart

universe u
variable {R G H : Type u} [CommRing R] [AddCommMonoid G] [AddCommMonoid H]
  (W : WeierstrassCurve R) (I : Ideal R) (hI : I ^ 2 = ⊥)

/-- The actual smooth-group point inserted from all ideal-valued character coordinates. -/
def point (q : G →₀ I) := (kernelEquiv W I hI (Multiplicative.ofAdd q)).val

/-- Character coordinates distinguish the original smooth-group kernel points. -/
theorem point_injective : Function.Injective (point (G := G) W I hI) := by
  intro p q h
  exact congrArg Multiplicative.toAdd ((kernelEquiv W I hI).injective (Subtype.ext h))

/-- Coordinate addition is the original smooth-group multiplication. -/
theorem point_add (p q : G →₀ I) :
    point W I hI (p + q) = point W I hI p * point W I hI q :=
  kernelEquiv_add W I hI p q

/-- Coordinate subtraction is the original smooth-group division. -/
theorem point_sub (p q : G →₀ I) :
    point W I hI (p - q) = point W I hI p / point W I hI q :=
  congrArg Subtype.val ((kernelEquiv W I hI).map_div
    (Multiplicative.ofAdd p) (Multiplicative.ofAdd q))

/-- Each inserted point retains exactly the specified identity reduction. -/
theorem point_reduction (q : G →₀ I) :
    smoothAlgebraReduction W (coefficientReduction R G I) (point W I hI q) = 1 :=
  kernelEquiv_reduction W I hI q

/-- Naturality for all character substitutions, including noninjective ones. -/
theorem point_natural (f : G →+ H) (q : G →₀ I) :
    smoothAlgebraReduction W (AddMonoidAlgebra.mapDomainAlgHom R R f) (point W I hI q) =
      point W I hI (Finsupp.lmapDomain I R f q) := by
  change smoothAlgebraReduction W _ (smoothInfinitesimalPoint W _ _ _) =
    smoothInfinitesimalPoint W _ _ _
  rw [smoothInfinitesimalPoint_natural W _ _ _
    (coefficientIdeal_sq_zero R G I hI) (coefficientIdeal_sq_zero R H I hI)
    (mapDomain_mem_coefficientIdeal R G H I f)]
  congr 1
  apply Subtype.ext
  exact fromIdealCoefficients_mapDomain R G H I f q

/-- The first projection retains the original first coface. -/
theorem point_first (q : G →₀ I) :
    smoothAlgebraReduction W (firstMap R G) (point W I hI q) =
      point W I hI (first R I G q) := point_natural W I hI _ q

/-- The second projection retains the original second coface. -/
theorem point_second (q : G →₀ I) :
    smoothAlgebraReduction W (secondMap R G) (point W I hI q) =
      point W I hI (second R I G q) := point_natural W I hI _ q

/-- Group multiplication retains the original diagonal character coface. -/
theorem point_diagonal (q : G →₀ I) :
    smoothAlgebraReduction W (diagonalMap R G) (point W I hI q) =
      point W I hI (diagonal R I G q) := point_natural W I hI _ q

/-- Projection onto the first pair retains all original coefficients. -/
theorem point_front (q : G × G →₀ I) :
    smoothAlgebraReduction W (frontMap R G) (point W I hI q) =
      point W I hI (front R I G q) := point_natural W I hI _ q

/-- Projection onto the last pair retains all original coefficients. -/
theorem point_back (q : G × G →₀ I) :
    smoothAlgebraReduction W (backMap R G) (point W I hI q) =
      point W I hI (back R I G q) := point_natural W I hI _ q

/-- Multiplication in the first pair retains all original coefficients. -/
theorem point_leftProduct (q : G × G →₀ I) :
    smoothAlgebraReduction W (leftProductMap R G) (point W I hI q) =
      point W I hI (leftProduct R I G q) := point_natural W I hI _ q

/-- Multiplication in the last pair retains all original coefficients. -/
theorem point_rightProduct (q : G × G →₀ I) :
    smoothAlgebraReduction W (rightProductMap R G) (point W I hI q) =
      point W I hI (rightProduct R I G q) := point_natural W I hI _ q

end FLT.Mazur.WeierstrassDiagonalizableInfinitesimalKernel

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassDiagonalizableCorrection

/-!
# Uniqueness of corrected diagonalizable maps

There are no nontrivial multiplicative maps into the square-zero Weierstrass
kernel: the full character boundary is injective. Consequently two corrected
maps with the same original reduction agree, independently of the underlying
scheme lifts used to construct them.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.WeierstrassDiagonalizableDefect

open DiagonalizableCobar WeierstrassIntegralChart
open WeierstrassDiagonalizableInfinitesimalKernel

universe u
variable {R G : Type u} [CommRing R] [AddCommMonoid G]
  (W : WeierstrassCurve R) (I : Ideal R) (hI : I ^ 2 = ⊥)

/-- Zero character coefficients give exactly the identity of the original smooth group. -/
theorem kernelPoint_zero : point (G := G) W I hI 0 = 1 :=
  congrArg Subtype.val ((kernelEquiv W I hI).map_one)

/-- A kernel point is the identity precisely when all original coefficients vanish. -/
theorem kernelPoint_eq_one (q : G →₀ I) : point W I hI q = 1 ↔ q = 0 := by
  constructor
  · intro h
    exact point_injective W I hI (h.trans (kernelPoint_zero W I hI).symm)
  · rintro rfl
    exact kernelPoint_zero W I hI

include hI in
/-- A multiplicative map into the full square-zero kernel must be the identity. -/
theorem multiplicative_kernel_eq_one (p : Points W (AddMonoidAlgebra R G))
    (hp : smoothAlgebraReduction W (coefficientReduction R G I) p = 1)
    (hm : defect W p = 1) : p = 1 := by
  obtain ⟨q, hq, _⟩ := existsUnique_coefficients W I hI ⟨p, hp⟩
  change point W I hI q = p at hq
  rw [← hq, defect_point] at hm
  have hb := (kernelPoint_eq_one W I hI _).mp hm
  have hz : q = 0 := boundary_injective R I G (hb.trans (map_zero _).symm)
  rw [← hq, hz, kernelPoint_zero]

include hI in
/-- Two multiplicative original scheme maps with the same reduction coincide. -/
theorem multiplicative_reduction_injective (p q : Points W (AddMonoidAlgebra R G))
    (hp : defect W p = 1) (hq : defect W q = 1)
    (hred : smoothAlgebraReduction W (coefficientReduction R G I) p =
      smoothAlgebraReduction W (coefficientReduction R G I) q) : p = q := by
  apply div_eq_one.mp
  apply multiplicative_kernel_eq_one W I hI
  · rw [map_div, hred, div_self']
  · rw [defect_div, hp, hq, div_self']

include hI in
/-- Every underlying lift has exactly one multiplicative correction with its reduction. -/
theorem existsUnique_corrected (p : Points W (AddMonoidAlgebra R G))
    (hp : defect W (smoothAlgebraReduction W (coefficientReduction R G I) p) = 1) :
    ∃! q : Points W (AddMonoidAlgebra R G),
      smoothAlgebraReduction W (coefficientReduction R G I) q =
        smoothAlgebraReduction W (coefficientReduction R G I) p ∧ defect W q = 1 := by
  refine ⟨corrected W I hI p hp,
    ⟨corrected_reduction W I hI p hp, corrected_defect W I hI p hp⟩, ?_⟩
  intro q hq
  exact multiplicative_reduction_injective W I hI q _ hq.2
    (corrected_defect W I hI p hp) (hq.1.trans (corrected_reduction W I hI p hp).symm)

/-- The actual correction is independent of the underlying scheme lift. -/
theorem corrected_independent_lift (p q : Points W (AddMonoidAlgebra R G))
    (hp : defect W (smoothAlgebraReduction W (coefficientReduction R G I) p) = 1)
    (hq : defect W (smoothAlgebraReduction W (coefficientReduction R G I) q) = 1)
    (hred : smoothAlgebraReduction W (coefficientReduction R G I) p =
      smoothAlgebraReduction W (coefficientReduction R G I) q) :
    corrected W I hI p hp = corrected W I hI q hq := by
  apply multiplicative_reduction_injective W I hI
  · exact corrected_defect W I hI p hp
  · exact corrected_defect W I hI q hq
  · rw [corrected_reduction, corrected_reduction, hred]

end FLT.Mazur.WeierstrassDiagonalizableDefect

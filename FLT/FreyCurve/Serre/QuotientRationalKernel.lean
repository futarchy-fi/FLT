/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.QuotientCoordinateHom

/-!
# Exact rational kernel and uniqueness of the descended coordinate maps

The base-change squares determine both rational maps uniquely. They also
identify the rational kernel exactly with the rational points of the geometric
Vélu kernel, strengthening the p-annihilation consequence used in assembly.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve.Velu

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] {n : ℕ} {hn : 0 < n}
variable {q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion n →ₗ[ZMod n] ZMod n}
variable {hodd : Odd n} {E' : WeierstrassCurve ℚ}
variable {hcurve : TorsionQuotientEquation E n hn q E'}

/-- A rational map descending the coordinate homomorphism has the exact geometric kernel. -/
theorem rational_quotient_kernel_iff (φ : (E⁄ℚ).Point →+ (E'⁄ℚ).Point)
    (hφ : ∀ a, Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) (φ a) =
      torsionQuotientPointHom E n hn q hodd E' hcurve
        (Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) a))
    (a : (E⁄ℚ).Point) :
    φ a = 0 ↔ Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) a ∈ torsionKernel E n q := by
  constructor
  · intro ha
    apply (torsionQuotientPointHom_eq_zero_iff E n hn q hodd E' hcurve _).mp
    rw [← hφ, ha, map_zero]
  · intro ha
    apply Affine.Point.map_injective (W' := E'.toAffine)
      (Algebra.ofId ℚ (AlgebraicClosure ℚ))
    change Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) (φ a) =
      Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) 0
    rw [hφ, map_zero]
    exact (torsionQuotientPointHom_eq_zero_iff E n hn q hodd E' hcurve _).mpr ha

/-- There is only one rational homomorphism descending the given geometric coordinate map. -/
theorem rational_quotient_map_unique (φ χ : (E⁄ℚ).Point →+ (E'⁄ℚ).Point)
    (hφ : ∀ a, Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) (φ a) =
      torsionQuotientPointHom E n hn q hodd E' hcurve
        (Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) a))
    (hχ : ∀ a, Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) (χ a) =
      torsionQuotientPointHom E n hn q hodd E' hcurve
        (Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) a)) : φ = χ := by
  ext a
  apply Affine.Point.map_injective (W' := E'.toAffine)
    (Algebra.ofId ℚ (AlgebraicClosure ℚ))
  exact (hφ a).trans (hχ a).symm

/-- The descended embedding of the quotient line is also uniquely determined. -/
theorem rational_quotient_torsion_unique (hq : Function.Surjective q)
    (f g : ZMod n →+ (E'⁄ℚ).Point)
    (hf : ∀ t, Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) (f (q t)) =
      torsionQuotientPointHom E n hn q hodd E' hcurve t.val)
    (hg : ∀ t, Affine.Point.baseChange ℚ (AlgebraicClosure ℚ) (g (q t)) =
      torsionQuotientPointHom E n hn q hodd E' hcurve t.val) : f = g := by
  ext x
  obtain ⟨t, rfl⟩ := hq x
  apply Affine.Point.map_injective (W' := E'.toAffine)
    (Algebra.ofId ℚ (AlgebraicClosure ℚ))
  exact (hf t).trans (hg t).symm

end WeierstrassCurve.Velu

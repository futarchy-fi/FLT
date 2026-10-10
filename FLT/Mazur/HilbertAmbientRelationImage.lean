/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertAmbientFactorization
public import FLT.Mazur.HilbertChartClassificationNaturality

/-!
# Independence of ambient equations from the chosen basis

The full image of the relation ideal depends only on the polynomial quotient
ideal. Testing modulo an arbitrary ideal retains nilpotents and proves equality
of equation ideals, rather than merely equality of their vanishing sets.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable (w v : Fin d → MvPolynomial I R) (K : Ideal (MvPolynomial I R))

/-- Cache coefficient rings for quotient tests of the relation equations. -/
local instance relationImageCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache each chart ring for quotient tests of the relation equations. -/
local instance relationImageChartRing (z : Fin d → MvPolynomial I R) :
    CommRing (ChartRing R I d z) := inferInstance

variable {S : Type*} [CommRing S] [Algebra R S]

/-- The point ideal of a composite into a quotient is the extension of the full point ideal. -/
theorem pointIdeal_quotient (f : ChartRing R I d w →ₐ[R] S) (L : Ideal S) :
    pointIdeal R I d w ((Ideal.Quotient.mkₐ R L).comp f) =
      (pointIdeal R I d w f).map (MvPolynomial.map (Ideal.Quotient.mk L)) := by
  exact congrArg Subtype.val (chartClassification_natural R I d w S (S ⧸ L) f)

/-- A quotient test detects containment of the entire image equation ideal. -/
theorem ambientRelationsIdeal_map_le_iff (f : ChartRing R I d w →ₐ[R] S) (L : Ideal S) :
    (ambientRelationsIdeal R I d w K).map f.toRingHom ≤ L ↔
      K.map (MvPolynomial.map (algebraMap R (S ⧸ L))) ≤
        (pointIdeal R I d w f).map (MvPolynomial.map (Ideal.Quotient.mk L)) := by
  rw [← pointIdeal_quotient R I d w f L,
    ← ambientRelationsIdeal_le_ker_point_iff, Ideal.map_le_iff_le_comap]
  have he : L.comap f.toRingHom =
      RingHom.ker ((Ideal.Quotient.mkₐ R L).comp f).toRingHom := by
    ext x
    change f x ∈ L ↔ Ideal.Quotient.mk L (f x) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.symm
  rw [he]

/-- Equal full polynomial ideals impose equal full ambient equation ideals in any basis. -/
theorem ambientRelationsIdeal_map_eq (f : ChartRing R I d w →ₐ[R] S)
    (g : ChartRing R I d v →ₐ[R] S)
    (h : pointIdeal R I d w f = pointIdeal R I d v g) :
    (ambientRelationsIdeal R I d w K).map f.toRingHom =
      (ambientRelationsIdeal R I d v K).map g.toRingHom := by
  apply le_antisymm
  · rw [ambientRelationsIdeal_map_le_iff R I d w K, h,
      ← ambientRelationsIdeal_map_le_iff R I d v K]
  · rw [ambientRelationsIdeal_map_le_iff R I d v K, ← h,
      ← ambientRelationsIdeal_map_le_iff R I d w K]

end FLT.Mazur.HilbertChart

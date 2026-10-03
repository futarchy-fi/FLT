/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.KummerCoefficientDescent

/-!
# Compatibility of root ratios with field refinement

Restriction of automorphisms and inclusion of units commute with root ratios.
Fixed unit ratios descend to the base field; this also controls root choices
and makes comparison independent of the finite Hilbert 90 field.
-/

@[expose] public section

namespace KummerTheory

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The multiplicative root ratio in units. -/
def unitRatio (b : Lˣ) (g : Gal(L/K)) : Lˣ := g • b / b

/-- The underlying field ratio. -/
@[simp] theorem coe_unitRatio (b : Lˣ) (g : Gal(L/K)) :
    (unitRatio b g : L) = g (b : L) / (b : L) := by
  simp [unitRatio, AlgEquiv.smul_units_def]

/-- Root ratios satisfy the multiplicative cocycle equation. -/
theorem unitRatio_isCocycle (b : Lˣ) : groupCohomology.IsMulCocycle₁ (unitRatio (K := K) b) := by
  intro g h
  simp only [unitRatio, smul_div', mul_smul]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Taking products of roots multiplies their ratios. -/
theorem unitRatio_mul (b d : Lˣ) (g : Gal(L/K)) :
    unitRatio (b * d) g = unitRatio b g * unitRatio d g := by
  simp only [unitRatio, smul_mul']
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Base-field rescaling leaves the ratio unchanged. -/
theorem unitRatio_base_mul (b : Lˣ) (t : Kˣ) (g : Gal(L/K)) :
    unitRatio (b * Units.map (algebraMap K L) t) g = unitRatio b g := by
  apply Units.ext
  simp only [coe_unitRatio, Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass]
  change g ((b : L) * algebraMap K L (t : K)) / _ = _
  rw [map_mul, AlgEquiv.commutes]
  change (g (b : L) * algebraMap K L (t : K)) /
    ((b : L) * algebraMap K L (t : K)) = g (b : L) / (b : L)
  exact mul_div_mul_right _ _ ((map_ne_zero (algebraMap K L)).mpr t.ne_zero)

/-- Root ratios commute with any equivariant field embedding. -/
theorem unitRatio_map {F : Type*} [Field F] [Algebra K F]
    (i : L →ₐ[K] F) (g : Gal(L/K)) (h : Gal(F/K))
    (heq : ∀ x, i (g x) = h (i x)) (b : Lˣ) :
    Units.map i (unitRatio b g) = unitRatio (Units.map i b) h := by
  apply Units.ext
  simp only [Units.coe_map, coe_unitRatio, MonoidHom.coe_ofClass]
  change i (g (b : L) / (b : L)) = h (i (b : L)) / i (b : L)
  rw [map_div₀, heq]

/-- In particular, refinement of a normal intermediate field preserves root ratios. -/
theorem unitRatio_restrict (E : IntermediateField K L) [Normal K E]
    (g : Gal(L/K)) (b : Eˣ) :
    Units.map E.val (unitRatio b (AlgEquiv.restrictNormalHom E g)) =
      unitRatio (Units.map E.val b) g :=
  unitRatio_map E.val _ g (fun x ↦ AlgEquiv.restrictNormal_commutes g E x) b

/-- A fixed unit of a Galois extension is the image of a base-field unit. -/
theorem exists_base_unit_of_fixed [IsGalois K L] (b : Lˣ)
    (hb : ∀ g : Gal(L/K), g • b = b) :
    ∃ t : Kˣ, Units.map (algebraMap K L) t = b := by
  obtain ⟨t, ht⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (b : L)).mpr
    (fun g ↦ congrArg (fun u : Lˣ ↦ (u : L)) (hb g))
  have ht0 : t ≠ 0 := fun h ↦ b.ne_zero (by rw [← ht, h, map_zero])
  exact ⟨Units.mk0 t ht0, Units.ext ht⟩

/-- Two roots with equal ratios differ by a base-field unit. -/
theorem unitRatio_eq_iff [IsGalois K L] (b d : Lˣ) :
    unitRatio (K := K) b = unitRatio d ↔
      ∃ t : Kˣ, d = b * Units.map (algebraMap K L) t := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := exists_base_unit_of_fixed (K := K) (d / b) (fun g ↦ by
      have hg := congrFun h g
      dsimp [unitRatio] at hg
      rw [smul_div']
      exact (div_eq_div_iff_mul_eq_mul).mpr (by
        have := (div_eq_div_iff_mul_eq_mul).mp hg
        simpa only [mul_comm, AlgEquiv.smul_units_def] using this.symm))
    exact ⟨t, by rw [ht]; simp⟩
  · rintro ⟨t, rfl⟩
    exact funext fun g ↦ (unitRatio_base_mul b t g).symm

end KummerTheory

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The faithful closed layer of an exact parameter pair

If the annihilator of u is (t), multiplication by u embeds the full
quotient by (t). If the annihilator of t is also (u), this embedding detects
all common annihilators of coordinates whose product is t.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ExactParameterLayer
variable {A : Type*} [CommRing A] (t u : A) (ht : u * t = 0)

/-- Multiplication by the last parameter power descends to its full quotient ring. -/
def layer : (A ⧸ Ideal.span {t}) →ₗ[A] A :=
  (Ideal.span {t}).liftQ (LinearMap.mulLeft A u) (by
    intro z hz
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    change u * (v * t) = 0
    rw [mul_left_comm, ht, mul_zero])

/-- The layer map is multiplication by the last parameter power on representatives. -/
theorem layer_mk (z : A) : layer t u ht (Ideal.Quotient.mk _ z) = u * z := rfl

/-- Multiplication by any original coordinate commutes with the layer map. -/
theorem layer_mul (x : A) (z : A ⧸ Ideal.span {t}) :
    layer t u ht (Ideal.Quotient.mk _ x * z) = x * layer t u ht z :=
  (layer t u ht).map_smul x z

/-- Exactness of the parameter annihilator makes the full quotient embed faithfully. -/
theorem layer_injective (ha : ∀ z : A, u * z = 0 ↔ ∃ w, t * w = z) :
    Function.Injective (layer t u ht) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z
  refine Quotient.inductionOn' z ?_
  intro w hw
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  obtain ⟨v, hv⟩ := (ha w).mp hw
  exact Ideal.mem_span_singleton.mpr ⟨v, hv.symm⟩

/-- Every parameter-annihilated element has a preimage in the original closed fiber. -/
theorem exists_layer (hb : ∀ z : A, t * z = 0 ↔ ∃ w, u * w = z)
    (z : A) (hz : t * z = 0) : ∃ w, layer t u ht w = z := by
  obtain ⟨w, hw⟩ := (hb z).mp hz
  exact ⟨Ideal.Quotient.mk _ w, hw⟩

/-- Coordinate annihilation is reflected by the faithful parameter layer. -/
theorem layer_mul_eq_zero_iff (ha : ∀ z : A, u * z = 0 ↔ ∃ w, t * w = z)
    (x : A) (z : A ⧸ Ideal.span {t}) :
    x * layer t u ht z = 0 ↔ Ideal.Quotient.mk _ x * z = 0 := by
  rw [← layer_mul]
  exact (map_eq_zero_iff _ (layer_injective t u ht ha))

/-- A common coordinate annihilator comes from a unique common annihilator in the closed fiber. -/
theorem socle_lift (ha : ∀ z : A, u * z = 0 ↔ ∃ w, t * w = z)
    (hb : ∀ z : A, t * z = 0 ↔ ∃ w, u * w = z)
    (x y : A) (hxy : x * y = t) (z : A) (hx : x * z = 0) (hy : y * z = 0) :
    ∃! w : A ⧸ Ideal.span {t}, layer t u ht w = z ∧
      Ideal.Quotient.mk _ x * w = 0 ∧ Ideal.Quotient.mk _ y * w = 0 := by
  have hz : t * z = 0 := by rw [← hxy, mul_right_comm, hx, zero_mul]
  obtain ⟨w, hw⟩ := exists_layer t u ht hb z hz
  refine ⟨w, ⟨hw, ?_, ?_⟩, ?_⟩
  · exact (layer_mul_eq_zero_iff t u ht ha x w).mp (hw ▸ hx)
  · exact (layer_mul_eq_zero_iff t u ht ha y w).mp (hw ▸ hy)
  · intro v hv
    exact layer_injective t u ht ha (hv.1.trans hw.symm)

end FLT.Mazur.ExactParameterLayer

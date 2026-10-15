/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The faithful parameter layer of a square-zero flat thickening

When the annihilator of t equals its image, multiplication by t embeds the
literal quotient by (t). Coordinate annihilators can be tested in that
quotient without discarding nilpotents in either ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.SquareZeroParameterLayer
variable {A : Type*} [CommRing A] (t : A) (ht : t * t = 0)

/-- Multiplication by the square-zero parameter descends to its full quotient ring. -/
def layer : (A ⧸ Ideal.span {t}) →ₗ[A] A :=
  (Ideal.span {t}).liftQ (LinearMap.mulLeft A t) (by
    intro z hz
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    change t * (u * t) = 0
    rw [mul_left_comm, ht, mul_zero])

/-- The layer map is multiplication by the original parameter on representatives. -/
theorem layer_mk (z : A) : layer t ht (Ideal.Quotient.mk _ z) = t * z := rfl

/-- Multiplication by any original coordinate commutes with the layer map. -/
theorem layer_mul (x : A) (z : A ⧸ Ideal.span {t}) :
    layer t ht (Ideal.Quotient.mk _ x * z) = x * layer t ht z :=
  (layer t ht).map_smul x z

/-- Exactness of the parameter annihilator makes the full quotient embed faithfully. -/
theorem layer_injective (ha : ∀ z : A, t * z = 0 ↔ ∃ w, t * w = z) :
    Function.Injective (layer t ht) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z
  refine Quotient.inductionOn' z ?_
  intro w hw
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  obtain ⟨v, hv⟩ := (ha w).mp hw
  exact Ideal.mem_span_singleton.mpr ⟨v, hv.symm⟩

/-- Every parameter-annihilated element has a preimage in the original closed fiber. -/
theorem exists_layer (ha : ∀ z : A, t * z = 0 ↔ ∃ w, t * w = z)
    (z : A) (hz : t * z = 0) : ∃ w, layer t ht w = z := by
  obtain ⟨w, hw⟩ := (ha z).mp hz
  exact ⟨Ideal.Quotient.mk _ w, hw⟩

/-- Coordinate annihilation is reflected by the faithful parameter layer. -/
theorem layer_mul_eq_zero_iff (ha : ∀ z : A, t * z = 0 ↔ ∃ w, t * w = z)
    (x : A) (z : A ⧸ Ideal.span {t}) :
    x * layer t ht z = 0 ↔ Ideal.Quotient.mk _ x * z = 0 := by
  rw [← layer_mul]
  exact (map_eq_zero_iff _ (layer_injective t ht ha))

/-- A common coordinate annihilator comes from a unique common annihilator in the closed fiber. -/
theorem socle_lift (ha : ∀ z : A, t * z = 0 ↔ ∃ w, t * w = z)
    (x y : A) (hxy : x * y = t) (z : A) (hx : x * z = 0) (hy : y * z = 0) :
    ∃! w : A ⧸ Ideal.span {t}, layer t ht w = z ∧
      Ideal.Quotient.mk _ x * w = 0 ∧ Ideal.Quotient.mk _ y * w = 0 := by
  have hz : t * z = 0 := by rw [← hxy, mul_right_comm, hx, zero_mul]
  obtain ⟨w, hw⟩ := exists_layer t ht ha z hz
  refine ⟨w, ⟨hw, ?_, ?_⟩, ?_⟩
  · exact (layer_mul_eq_zero_iff t ht ha x w).mp (hw ▸ hx)
  · exact (layer_mul_eq_zero_iff t ht ha y w).mp (hw ▸ hy)
  · intro v hv
    exact layer_injective t ht ha (hv.1.trans hw.symm)

end FLT.Mazur.SquareZeroParameterLayer

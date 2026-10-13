/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Finite original coefficients defining an equality locus

In a Noetherian ambient ring, equality of two arbitrary coefficient maps is
cut out by finitely many of the original coefficient differences. The source
ring need not be Noetherian or finitely generated. The equations detect maps
to every commutative ring, including nonreduced rings.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteCoefficientDifference
universe u v w
variable {B : Type u} {T : Type v} [CommRing B] [CommRing T]
  (l r : B →+* T)

/-- The ideal of all original coefficient differences. -/
def differenceIdeal : Ideal T := Ideal.span (Set.range fun b ↦ l b - r b)

/-- An ambient ring map kills the difference ideal exactly when it equalizes all coefficients. -/
theorem differenceIdeal_le_ker_iff {C : Type w} [CommRing C] (g : T →+* C) :
    differenceIdeal l r ≤ RingHom.ker g ↔ g.comp l = g.comp r := by
  rw [differenceIdeal, Ideal.span_le]
  constructor
  · intro h
    ext b
    have hb := h (Set.mem_range_self b)
    change g (l b - r b) = 0 at hb
    simpa only [map_sub, sub_eq_zero, RingHom.comp_apply] using hb
  · intro h t ht
    obtain ⟨b, rfl⟩ := ht
    change g (l b - r b) = 0
    rw [map_sub, sub_eq_zero]
    exact DFunLike.congr_fun h b

/-- Finitely many original differences generate the entire equality ideal. -/
theorem exists_finite_differences [IsNoetherianRing T] :
    ∃ s : Finset B, differenceIdeal l r =
      Ideal.span ((fun b ↦ l b - r b) '' (s : Set B)) := by
  classical
  obtain ⟨t, ht, he⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset
      (R := T) (Set.range fun b ↦ l b - r b)).mp
        (differenceIdeal l r).fg_of_isNoetherianRing
  choose b hb using fun x : t ↦ ht x.property
  let s : Finset B := Finset.univ.image b
  refine ⟨s, ?_⟩
  change Ideal.span (Set.range fun b ↦ l b - r b) = _
  change Ideal.span (Set.range fun b ↦ l b - r b) = Ideal.span (t : Set T) at he
  rw [he]
  congr 1
  ext x
  constructor
  · intro hx
    exact ⟨b ⟨x, hx⟩, Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩,
      hb ⟨x, hx⟩⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hy
    rw [hb z]
    exact z.property

/-- A finite subset of the original coefficients defining the full equality locus. -/
def coefficients [IsNoetherianRing T] : Finset B :=
  (exists_finite_differences l r).choose

/-- The chosen finite equations generate exactly the original equality ideal. -/
theorem differenceIdeal_eq [IsNoetherianRing T] :
    differenceIdeal l r =
      Ideal.span ((fun b ↦ l b - r b) '' (coefficients l r : Set B)) :=
  (exists_finite_differences l r).choose_spec

/-- The finite equations detect equality on every ring-valued test, including nilpotents. -/
theorem equalizes_iff_coefficients [IsNoetherianRing T]
    {C : Type w} [CommRing C] (g : T →+* C) :
    g.comp l = g.comp r ↔ ∀ b ∈ coefficients l r, g (l b) = g (r b) := by
  rw [← differenceIdeal_le_ker_iff, differenceIdeal_eq, Ideal.span_le]
  constructor
  · intro h b hb
    have hzero := h ⟨b, hb, rfl⟩
    change g (l b - r b) = 0 at hzero
    simpa only [map_sub, sub_eq_zero] using hzero
  · intro h t ht
    obtain ⟨b, hb, rfl⟩ := ht
    change g (l b - r b) = 0
    rw [map_sub, sub_eq_zero]
    exact h b hb

end FLT.Mazur.FiniteCoefficientDifference

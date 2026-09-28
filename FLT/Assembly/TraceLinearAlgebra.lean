/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.TraceLeaves
public import FLT.KnownIn1980s.Ribet_Lemma.Defs

/-!
# Traces of extensions with a trivial character

In dimension two, either a fixed line or a trivial line quotient forces one
eigenvalue to be one. The trace is then one plus the determinant.
-/

@[expose] public section

namespace StableLattice

/-- An extension with a trivial subcharacter or quotient character has
trace one plus determinant. -/
theorem IsExtensionOf.trace_eq_one_add_det_of_trivial_character
    {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {ρ : Representation K G V} {ψ₁ ψ₂ : G →* Kˣ}
    (h : IsExtensionOf ρ ψ₁ ψ₂) (hdim : Module.finrank K V = 2)
    (htrivial : ψ₁ = 1 ∨ ψ₂ = 1) (g : G) :
    LinearMap.trace K V (ρ g) = 1 + LinearMap.det (ρ g) := by
  obtain ⟨L, hL, hsub, hquot⟩ := h
  have hsing : LinearMap.det (ρ g - 1) = 0 := by
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot]
    intro hker
    have hinj := LinearMap.ker_eq_bot.mp hker
    rcases htrivial with rfl | rfl
    · obtain ⟨v, hv, _⟩ := finrank_eq_one_iff'.mp hL
      apply hv
      apply Subtype.ext
      apply hinj
      simpa using sub_eq_zero.mpr (hsub g v v.property)
    · have hsurj : Function.Surjective (ρ g - 1 : Module.End K V) :=
        LinearMap.injective_iff_surjective.mp hinj
      have htop : L = ⊤ := by
        apply top_unique
        intro v _
        obtain ⟨w, rfl⟩ := hsurj v
        simpa using hquot g w
      rw [htop, finrank_top, hdim] at hL
      omega
  let b := Module.finBasisOfFinrankEq K V hdim
  rw [LinearMap.trace_eq_matrix_trace K b, ← LinearMap.det_toMatrix b]
  rw [← LinearMap.det_toMatrix b, map_sub, LinearMap.toMatrix_one] at hsing
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.sub_apply,
    Matrix.one_apply, Fin.isValue, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff,
    Nat.reduceEqDiff, ↓reduceIte] at hsing ⊢
  linear_combination -hsing

end StableLattice

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.ScalarCharacterKernel
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Frobenius detects higher-dimensional simple scalar actions

If every value of an extracted scalar character is fixed by prime-field
Frobenius, every prime-field line is invariant. Irreducibility therefore
forces dimension one. In dimension two the conjugate character is distinct.
-/

@[expose] public noncomputable section
namespace Representation

variable {p : ℕ} [Fact p.Prime] {F G V : Type*} [Field F] [CharP F p]
  [Group G] [AddCommGroup V] [Module (ZMod p) V] [Module F V]
  (ρ : Representation (ZMod p) G V) [IsIrreducible ρ]

/-- A Frobenius-fixed scalar character on a simple representation forces a line. -/
theorem finrank_eq_one_of_scalar_character_frobenius
    (hdim : Module.finrank F V = 1) (χ : G →* Fˣ)
    (hχ : ∀ g x, ρ g x = (χ g : F) • x) (hfix : χ ^ p = χ) :
    Module.finrank (ZMod p) V = 1 := by
  let e : F ≃ₗ[F] V := (Module.nonempty_linearEquiv_of_finrank_eq_one hdim).some
  have hv : e 1 ≠ 0 := fun h ↦ one_ne_zero (e.injective (h.trans e.map_zero.symm))
  let L : Subrepresentation ρ := {
    toSubmodule := Submodule.span (ZMod p) {e 1}
    apply_mem_toSubmodule := by
      intro g x hx
      have hg : (χ g : F) ^ p = (χ g : F) :=
        congrArg (fun f : G →* Fˣ ↦ (f g : F)) hfix
      obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p F).mp
        ((Subfield.mem_bot_iff_pow_eq_self F p).mpr hg)
      rw [hχ, ← hn, Int.cast_smul_eq_zsmul]
      exact (Submodule.span (ZMod p) {e 1}).toAddSubgroup.zsmul_mem hx n }
  have hL : L ≠ ⊥ := by
    intro h
    have hm : e 1 ∈ L := Submodule.subset_span (Set.mem_singleton _)
    rw [h] at hm
    exact hv hm
  have ht : L = ⊤ := (eq_bot_or_eq_top L).resolve_left hL
  apply finrank_eq_one_iff'.mpr
  refine ⟨e 1, hv, fun w ↦ ?_⟩
  have hw : w ∈ L := by rw [ht]; trivial
  exact Submodule.mem_span_singleton.mp hw

/-- A simple rank-two prime-field action has two distinct scalar conjugate characters. -/
theorem scalar_character_frobenius_ne (hdim : Module.finrank F V = 1)
    (χ : G →* Fˣ) (hχ : ∀ g x, ρ g x = (χ g : F) • x)
    (hV : Module.finrank (ZMod p) V = 2) : χ ^ p ≠ χ := by
  intro hf
  have h := ρ.finrank_eq_one_of_scalar_character_frobenius hdim χ hχ hf
  omega

end Representation

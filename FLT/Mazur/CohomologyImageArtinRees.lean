/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicCohomologyFiltration

/-!
# Artin-Rees on each fixed cohomology image

Proper finiteness allows algebraic Artin-Rees on every actual image submodule.
For a fixed image, its induced base-adic topology agrees with its own adic
topology. The constants here can depend on that fixed image; this does not
assert stability of the varying cohomology image filtration.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.Chow.AffineBase

namespace FLT.Mazur.BaseAdicCohomology

variable {R : CommRingCat.{0}} [IsNoetherianRing R]
  {X : Scheme.{0}} (f : X ⟶ Spec R) [IsProper f] (J : Ideal R)
  (M : X.Modules) [M.IsFinitePresentation]

/-- Algebraic Artin-Rees applies to each actual proper cohomology image. -/
theorem image_artinRees (q b : ℕ) :
    ∃ c : ℕ, ∀ n ≥ c,
      J ^ n • ⊤ ⊓ (imageFiltration f J M q).N b =
        J ^ (n - c) • (J ^ c • ⊤ ⊓ (imageFiltration f J M q).N b) := by
  let _ := proper_coherent_hasFiniteRingCohomology f M q
  exact J.exists_pow_inf_eq_pow_smul ((imageFiltration f J M q).N b)

/-- For a fixed image, a shifted induced adic neighborhood is contained in its own one. -/
theorem image_induced_adic_le (q b : ℕ) :
    ∃ c : ℕ, ∀ n : ℕ,
      J ^ (n + c) • ⊤ ⊓ (imageFiltration f J M q).N b ≤
        J ^ n • (imageFiltration f J M q).N b := by
  obtain ⟨c, hc⟩ := image_artinRees f J M q b
  refine ⟨c, fun n ↦ ?_⟩
  rw [hc (n + c) (Nat.le_add_left c n), Nat.add_sub_cancel]
  exact smul_mono_right _ inf_le_right

/-- The intrinsic adic neighborhood is always contained in the induced one. -/
lemma image_adic_le_induced (q b n : ℕ) :
    J ^ n • (imageFiltration f J M q).N b ≤
      J ^ n • ⊤ ⊓ (imageFiltration f J M q).N b :=
  le_inf (smul_mono_right _ le_top) Submodule.smul_le_right

/-- Both neighborhood containments, with one uniform shift for each fixed image. -/
theorem image_adic_cofinal (q b : ℕ) :
    ∃ c : ℕ, ∀ n : ℕ,
      J ^ (n + c) • ⊤ ⊓ (imageFiltration f J M q).N b ≤
        J ^ n • (imageFiltration f J M q).N b ∧
      J ^ n • (imageFiltration f J M q).N b ≤
        J ^ n • ⊤ ⊓ (imageFiltration f J M q).N b := by
  obtain ⟨c, hc⟩ := image_induced_adic_le f J M q b
  exact ⟨c, fun n ↦ ⟨hc n, image_adic_le_induced f J M q b n⟩⟩

end FLT.Mazur.BaseAdicCohomology

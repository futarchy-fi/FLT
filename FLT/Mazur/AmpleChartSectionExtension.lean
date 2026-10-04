/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPowerGluing
public import FLT.Mazur.AmpleCommonDegree

/-!
# Extending chart functions by powers of their generating section

On a finite affine section cover, every regular function on one chart extends
as a section of a tensor power after multiplication by the chart generator.
The proof clears denominators and overlap kernels over arbitrary rings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback SectionCover
variable {X : Scheme.{u}} {L : X.Modules} {ι : Type v}

/-- A chart function extends after multiplication by a power of its section generator. -/
theorem sectionCover_extension [Finite ι] (s : ι → Γ(L, ⊤))
    (haff : ∀ j, IsAffineOpen (chart s j)) (hcover : ⨆ j, chart s j = ⊤)
    (i : ι) (a : Γ(X, chart s i)) :
    ∃ (N : ℕ) (σ : Γ(tensorPower L N, ⊤)),
      (tensorPower L N).presheaf.map (homOfLE (show chart s i ≤ ⊤ from le_top)).op σ =
        a • powerFrame s N i (chart s i) := by
  obtain ⟨N, b, hb, hc⟩ := compatible_numerators s haff i a
  obtain ⟨σ, hσ⟩ := glue_powerSection s hcover N b hc
  refine ⟨N, σ, ?_⟩
  rw [hσ i]
  have hi : b i = a := by
    have hi := congrArg (res (le_inf le_rfl le_rfl)) (hb i)
    simp only [sectionRatioOn_self, one_pow, one_mul,
      res_res] at hi
    simpa [res] using hi
  rw [hi]

/-- A chart function extends in every sufficiently large tensor degree. -/
theorem sectionCover_eventually_extension [Finite ι] (s : ι → Γ(L, ⊤))
    (haff : ∀ j, IsAffineOpen (chart s j)) (hcover : ⨆ j, chart s j = ⊤)
    (i : ι) (a : Γ(X, chart s i)) :
    ∃ N : ℕ, ∀ D ≥ N, ∃ σ : Γ(tensorPower L D, ⊤),
      (tensorPower L D).presheaf.map (homOfLE (show chart s i ≤ ⊤ from le_top)).op σ =
        a • powerFrame s D i (chart s i) := by
  obtain ⟨N, hN⟩ := eventually_compatible_numerators s haff i a
  refine ⟨N, fun D hD ↦ ?_⟩
  obtain ⟨b, hb, hc⟩ := hN D hD
  obtain ⟨σ, hσ⟩ := glue_powerSection s hcover D b hc
  refine ⟨σ, ?_⟩
  rw [hσ i]
  have hi := congrArg (res (le_inf le_rfl le_rfl)) (hb i)
  simp only [sectionRatioOn_self, one_pow, one_mul, res_res] at hi
  have hi' : b i = a := by simpa [res] using hi
  rw [hi']

/-- A finite family of chart functions extends in one positive tensor degree. -/
theorem sectionCover_finite_extension [Finite ι] (s : ι → Γ(L, ⊤))
    (haff : ∀ j, IsAffineOpen (chart s j)) (hcover : ⨆ j, chart s j = ⊤)
    {κ : Type*} [Finite κ] (i : κ → ι) (a : ∀ k, Γ(X, chart s (i k))) :
    ∃ (D : ℕ) (_ : 0 < D) (σ : κ → Γ(tensorPower L D, ⊤)), ∀ k,
      (tensorPower L D).presheaf.map (homOfLE (show chart s (i k) ≤ ⊤ from le_top)).op (σ k) =
        a k • powerFrame s D (i k) (chart s (i k)) := by
  classical
  let := Fintype.ofFinite κ
  choose N hN using fun k ↦ sectionCover_eventually_extension s haff hcover (i k) (a k)
  let D := Finset.univ.sup N + 1
  have hD (k : κ) : N k ≤ D := (Finset.le_sup (Finset.mem_univ k)).trans (Nat.le_succ _)
  choose σ hσ using fun k ↦ hN k D (hD k)
  exact ⟨D, Nat.succ_pos _, σ, hσ⟩

/-- Every ample sheaf admits a positive-power affine cover whose chart functions extend. -/
theorem AmpleLineBundle.section_cover_with_extension (hL : AmpleLineBundle L) :
    ∃ (κ : Type u) (_ : Finite κ) (d : ℕ) (_ : 0 < d)
      (s : κ → Γ(tensorPower L d, ⊤)),
      (∀ i, IsAffineOpen (chart s i)) ∧ (⨆ i, chart s i) = ⊤ ∧
      ∀ (i : κ) (a : Γ(X, chart s i)),
        ∃ (N : ℕ) (σ : Γ(tensorPower (tensorPower L d) N, ⊤)),
          (tensorPower (tensorPower L d) N).presheaf.map
            (homOfLE (show chart s i ≤ ⊤ from le_top)).op σ =
              a • powerFrame s N i (chart s i) := by
  obtain ⟨κ, hκ, d, hd, s, haff, hcover⟩ := hL.common_degree_section_cover
  let := hκ
  exact ⟨κ, hκ, d, hd, s, haff, hcover, sectionCover_extension s haff hcover⟩

end FLT.Mazur.FCurve

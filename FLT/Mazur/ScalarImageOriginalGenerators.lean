/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarExtensionImageReduction

/-!
# Finite extended images have generators from original source elements

Finiteness after localization need not descend to finiteness of the original
image. Nevertheless, finitely many original source elements generate the
extended image. This provides the original representatives needed for
simultaneous denominator clearing and chart correction constructions.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ScalarImageOriginalGenerators
variable {R D M : Type*} [CommRing R]
  [AddCommGroup D] [Module R D] [AddCommGroup M] [Module R M]
  (g : D →ₗ[R] M) (S : Type*) [CommRing S] [Algebra R S]

/-- Unit tensors of original image values span the entire scalar-extended image. -/
theorem range_eq_span : LinearMap.range (g.baseChange S) =
    Submodule.span S (Set.range (fun t : D ↦ (1 ⊗ₜ[R] g t : S ⊗[R] M))) := by
  rw [CompatibleErrorBaseChange.range_baseChange, Submodule.baseChange_eq_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨g t, ⟨t, rfl⟩, rfl⟩

/-- Finite local images have a finite generating family of original source values. -/
theorem exists_original_generators (hfg : (LinearMap.range (g.baseChange S)).FG) :
    ∃ (n : ℕ) (t : Fin n → D),
      Submodule.span S (Set.range (fun i ↦ (1 ⊗ₜ[R] g (t i) : S ⊗[R] M))) =
        LinearMap.range (g.baseChange S) := by
  rw [range_eq_span] at hfg
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg
  obtain ⟨n, v, hv⟩ := s.finite_toSet.fin_embedding
  have hmem : ∀ i, v i ∈ Set.range (fun t : D ↦ (1 ⊗ₜ[R] g t : S ⊗[R] M)) := by
    intro i
    apply hs
    rw [← hv]
    exact ⟨i, rfl⟩
  choose t ht using hmem
  refine ⟨n, t, ?_⟩
  rw [show (fun i ↦ (1 ⊗ₜ[R] g (t i) : S ⊗[R] M)) = v from funext ht,
    hv, ← hspan, ← range_eq_span]

/-- Finite generation over the new scalars is exactly a finite original-value spanning test. -/
theorem fg_iff_original_generators :
    (LinearMap.range (g.baseChange S)).FG ↔ ∃ (n : ℕ) (t : Fin n → D),
      Submodule.span S (Set.range (fun i ↦ (1 ⊗ₜ[R] g (t i) : S ⊗[R] M))) =
        LinearMap.range (g.baseChange S) := by
  constructor
  · exact exists_original_generators g S
  · rintro ⟨n, t, h⟩
    rw [← h]
    exact Submodule.fg_span (Set.finite_range _)

end FLT.Mazur.ScalarImageOriginalGenerators

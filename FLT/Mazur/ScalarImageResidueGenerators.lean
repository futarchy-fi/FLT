/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SourceImageResidueRestriction
public import FLT.Mazur.LocalizedImageFiniteLifts

/-!
# Original relative source frames from residue generators

A finite original family spanning the local source modulo restrictions and
the maximal ideal already spans modulo restrictions alone, provided the local
connecting image is finite. Its exact lift test then uses original numerators
and a single original denominator.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ScalarImageResidueGenerators
variable {R U D M : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup D] [Module R D]
  [AddCommGroup M] [Module R M]
  (ρ : U →ₗ[R] D) (g : D →ₗ[R] M)
  (hker : LinearMap.ker g = LinearMap.range ρ)
  (S : Type*) [CommRing S] [Algebra R S] [Module.Flat R S] [IsLocalRing S]

include hker in
/-- Residue source generators lift to an actual relative source frame over the local ring. -/
theorem source_span {n : ℕ} (t : Fin n → D)
    (hfg : (LinearMap.range (g.baseChange S)).FG)
    (hres : Submodule.span S (Set.range (fun j ↦ (1 ⊗ₜ[R] t j : S ⊗[R] D))) ⊔
      LinearMap.range (ρ.baseChange S) ⊔
        IsLocalRing.maximalIdeal S • (⊤ : Submodule S (S ⊗[R] D)) = ⊤) :
    Submodule.span S (Set.range (fun j ↦ (1 ⊗ₜ[R] t j : S ⊗[R] D))) ⊔
      LinearMap.range (ρ.baseChange S) = ⊤ :=
  SourceImageNakayama.source_span_of_residue (ρ.baseChange S) (g.baseChange S)
    (ScalarImageSourceGenerators.ker_baseChange ρ g hker S) hfg _ _
    (IsLocalRing.maximalIdeal_le_jacobson ⊥) hres

include hker in
/-- Source residue restriction surjectivity kills the finite local connecting image. -/
theorem eq_zero_of_residueRestriction
    (hfg : (LinearMap.range (g.baseChange S)).FG)
    (hres : Function.Surjective (SourceImageNakayama.residueRestriction
      (ρ.baseChange S) (IsLocalRing.maximalIdeal S))) : g.baseChange S = 0 :=
  SourceImageNakayama.eq_zero_of_residue (ρ.baseChange S) (g.baseChange S)
    (ScalarImageSourceGenerators.ker_baseChange ρ g hker S) hfg _
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    ((SourceImageNakayama.residueRestriction_surjective_iff _ _).mp hres)

include hker in
omit [Module.Flat R S] in
/-- A residue source frame gives a common original denominator for every exact finite lift. -/
theorem eq_zero_iff_finite_lifts (V : Submonoid R) [IsLocalization V S]
    {n : ℕ} (t : Fin n → D) (hfg : (LinearMap.range (g.baseChange S)).FG)
    (hres : Submodule.span S (Set.range (fun j ↦ (1 ⊗ₜ[R] t j : S ⊗[R] D))) ⊔
      LinearMap.range (ρ.baseChange S) ⊔
        IsLocalRing.maximalIdeal S • (⊤ : Submodule S (S ⊗[R] D)) = ⊤) :
    g.baseChange S = 0 ↔ ∃ (a : V) (v : Fin n → U), ∀ j, ρ (v j) = a.val • t j := by
  let _ : Module.Flat R S := IsLocalization.flat S V
  exact LocalizedImageFiniteLifts.eq_zero_iff_finite_lifts ρ g hker V S t
    (source_span ρ g hker S t hfg hres)

end FLT.Mazur.ScalarImageResidueGenerators

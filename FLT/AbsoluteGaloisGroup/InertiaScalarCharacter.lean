/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudInertiaSimpleScalars
public import FLT.Deformations.RepresentationTheory.ScalarCharacterFrobenius
public import FLT.Deformations.RepresentationTheory.SimpleScalarDegree
public import FLT.Deformations.RepresentationTheory.CharacterRange

/-!
# Scalar characters extracted from continuous simple inertia representations

The scalar field and character come from the given representation. Its
kernel, continuity, cardinality and distinct Frobenius conjugate are proved.
The kernel comparison with a specified uniformizer-root character is separate.
-/

@[expose] public noncomputable section
namespace LocalRamification
open NumberField IsLocalRing

universe u
variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  {V : Type u} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
  (ρ : Representation (ZMod p) (localInertiaGroup v) V) [ρ.IsIrreducible]
  [TopologicalSpace (Module.End (ZMod p) V)ˣ]
  [DiscreteTopology (Module.End (ZMod p) V)ˣ]

omit [CharP (ResidueField (v.adicCompletionIntegers K)) p] [Finite V] [ρ.IsIrreducible] in
/-- A character with the same kernel as a continuous discrete representation is continuous. -/
theorem inertia_scalar_character_continuous {F : Type*} [Field F]
    [TopologicalSpace Fˣ] (χ : localInertiaGroup v →* Fˣ)
    (hker : χ.ker = ρ.toHomUnits.ker) (hρ : Continuous ρ.toHomUnits) : Continuous χ := by
  let f := ρ.toHomUnits.factorThroughRange χ hker.ge
  have hf : Continuous f := continuous_of_discreteTopology
  have hr : Continuous ρ.toHomUnits.rangeRestrict := hρ.subtype_mk _
  exact (hf.comp hr).congr fun g ↦ ρ.toHomUnits.factorThroughRange_apply χ hker.ge g

/-- Construct the actual quadratic scalar character of a simple rank-two inertia action. -/
theorem exists_niveauTwo_scalar_character (hρ : Continuous ρ.toHomUnits)
    (hV : Module.finrank (ZMod p) V = 2) :
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F p) (_ : Module F V)
      (χ : localInertiaGroup v →* Fˣ),
      Module.finrank F V = 1 ∧ Nat.card F = p * p ∧
      (∀ g x, ρ g x = (χ g : F) • x) ∧ χ.ker = ρ.toHomUnits.ker ∧ χ ^ p ≠ χ := by
  obtain ⟨F, hF, hfin, hp, hmod, hdim, hcomm⟩ :=
    exists_rank_one_scalar_field_of_local_inertia v p ρ hρ
  obtain ⟨χ, hχ, hker⟩ := ρ.exists_scalar_character_with_kernel hdim hcomm
  exact ⟨F, hF, hfin, hp, hmod, χ, hdim,
    Representation.scalar_card_of_prime_finrank_two hdim hV, hχ, hker,
    ρ.scalar_character_frobenius_ne hdim χ hχ hV⟩

end LocalRamification

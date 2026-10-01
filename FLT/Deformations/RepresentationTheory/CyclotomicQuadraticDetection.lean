/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import FLT.AbsoluteGaloisGroup.LocalCyclotomicCharacter
public import FLT.Deformations.RepresentationTheory.CharacterRange
public import FLT.Deformations.RepresentationTheory.CyclicRestrictionTwist
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Quadratic detection on the global cyclotomic quotient

The kernel quotient of the mod-p cyclotomic character is finite and cyclic.
A generator of its image simultaneously detects all nontrivial quadratic
characters trivial on the kernel, including the self-twist from reducible
restriction. The detecting element is global; membership in local inertia
still requires the local cyclotomic surjectivity theorem.
-/

@[expose] public noncomputable section

namespace CyclotomicQuadratic

variable (p : ℕ) [Fact p.Prime]

/-- The global mod-p cyclotomic character over the rationals. -/
def character : Field.absoluteGaloisGroup ℚ →* (ZMod p)ˣ :=
  (modularCyclotomicCharacter (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity _ p)).comp
      { toFun := fun σ ↦ σ.toRingEquiv
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl }

/-- Restricting the global character to the chosen local inertia embedding
agrees with the local modular cyclotomic character. -/
theorem character_map_local
    (σ : localInertiaGroup (LocalCyclotomic.rationalPlace p)) :
    character p (Field.absoluteGaloisGroup.map
      (algebraMap ℚ ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)) σ.1) =
      LocalCyclotomic.inertiaCharacter p σ := by
  exact modularCyclotomicCharacter.naturality
    (AlgebraicClosure.map
      (algebraMap ℚ ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)))
    (Field.absoluteGaloisGroup.map
      (algebraMap ℚ ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)) σ.1).toRingEquiv
    σ.1.toRingEquiv (fun x ↦ Field.absoluteGaloisGroup.lift_map _ σ.1 x) _ _

/-- Finiteness of the cyclotomic kernel quotient, obtained from the image. -/
instance finite_quotient_ker : Finite (Field.absoluteGaloisGroup ℚ ⧸ (character p).ker) :=
  Finite.of_injective (QuotientGroup.quotientKerEquivRange (character p))
    (QuotientGroup.quotientKerEquivRange (character p)).injective

/-- Cyclicity of the cyclotomic kernel quotient, obtained from the image. -/
instance isCyclic_quotient_ker : IsCyclic (Field.absoluteGaloisGroup ℚ ⧸ (character p).ker) :=
  isCyclic_of_injective (QuotientGroup.quotientKerEquivRange (character p)).toMonoidHom
    (QuotientGroup.quotientKerEquivRange (character p)).injective

variable {k : Type*} [Field k]

/-- Every lift of a cyclotomic image generator detects each quadratic character
that is nontrivial and trivial on the cyclotomic kernel. -/
theorem eq_neg_one_of_generator (χ : Field.absoluteGaloisGroup ℚ →* kˣ)
    (hχ : χ ≠ 1) (hker : ∀ g : (character p).ker, χ g = 1)
    (hsq : ∀ g, χ g ^ 2 = 1) (t : Field.absoluteGaloisGroup ℚ)
    (ht : ∀ a : (character p).range, a ∈ Subgroup.zpowers ((character p).rangeRestrict t)) :
    χ t = -1 :=
  (character p).quadratic_eq_neg_one_of_range_generator χ
    (fun g hg ↦ hker ⟨g, hg⟩) hχ hsq t ht

/-- One global element detects all nontrivial quadratic characters of the quotient. -/
theorem exists_simultaneous_detector :
    ∃ t : Field.absoluteGaloisGroup ℚ,
      ∀ χ : Field.absoluteGaloisGroup ℚ →* kˣ, χ ≠ 1 →
        (∀ g : (character p).ker, χ g = 1) → (∀ g, χ g ^ 2 = 1) → χ t = -1 := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := (character p).range)
  obtain ⟨t, ht⟩ := (character p).rangeRestrict_surjective a
  exact ⟨t, fun χ hχ hker hsq ↦ eq_neg_one_of_generator p χ hχ hker hsq t (ht ▸ ha)⟩

variable {V : Type*} [IsAlgClosed k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- Apply the cyclic restriction theorem to the actual cyclotomic kernel and
construct a global element detecting its quadratic self-twist. -/
theorem exists_detected_selfTwist (ρ : Representation k (Field.absoluteGaloisGroup ℚ) V)
    (hV : Module.finrank k V = 2) (hchar : (2 : k) ≠ 0) (hirr : ρ.IsIrreducible)
    (hres : ¬ Representation.IsIrreducible (ρ.comp (character p).ker.subtype)) :
    ∃ χ : Field.absoluteGaloisGroup ℚ →* kˣ,
      χ ≠ 1 ∧ (∀ g : (character p).ker, χ g = 1) ∧ (∀ g, χ g ^ 2 = 1) ∧
      (∃ e : V ≃ₗ[k] V, ∀ g, e.conj (ρ g) = (χ g : k) • ρ g) ∧
      ∃ t : Field.absoluteGaloisGroup ℚ, χ t = -1 := by
  obtain ⟨χ, hχ, hker, hsq, e, he⟩ :=
    ρ.exists_quadratic_selfTwist (character p).ker hV hchar hirr hres
  obtain ⟨t, ht⟩ := exists_simultaneous_detector (k := k) p
  exact ⟨χ, hχ, hker, hsq, ⟨e, he⟩, t, ht χ hχ hker hsq⟩

end CyclotomicQuadratic

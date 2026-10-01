/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import FLT.AbsoluteGaloisGroup.LocalCyclotomicSurjectivity
public import FLT.Deformations.RepresentationTheory.CyclotomicQuadraticDetection

/-!
# Quadratic detection by an actual inertia element

Local cyclotomic surjectivity supplies one inertia element detecting every
nontrivial quadratic character of the global cyclotomic quotient. Apply this
to the self-twist arising from reducible restriction.
-/

@[expose] public noncomputable section

namespace CyclotomicQuadratic

variable (p : ℕ) [Fact p.Prime] {k : Type*} [Field k]

/-- One actual local inertia element detects all quadratic characters of the quotient. -/
theorem exists_inertia_detector :
    ∃ t : localInertiaGroup (LocalCyclotomic.rationalPlace p),
      ∀ χ : Field.absoluteGaloisGroup ℚ →* kˣ, χ ≠ 1 →
        (∀ g : (character p).ker, χ g = 1) → (∀ g, χ g ^ 2 = 1) →
        χ (Field.absoluteGaloisGroup.map
          (algebraMap ℚ ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)) t.1) = -1 := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  obtain ⟨t, ht⟩ := LocalCyclotomic.inertiaCharacter_surjective p a
  refine ⟨t, fun χ hχ hker hsq ↦ eq_neg_one_of_generator p χ hχ hker hsq _ ?_⟩
  intro b
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (ha b.1)
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨n, Subtype.ext ?_⟩
  change character p (Field.absoluteGaloisGroup.map
    (algebraMap ℚ ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)) t.1) ^ n = b.1
  rwa [character_map_local, ht]

variable {V : Type*} [IsAlgClosed k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- The cyclotomic self-twist is detected on local inertia at p. -/
theorem exists_inertia_detected_selfTwist
    (ρ : Representation k (Field.absoluteGaloisGroup ℚ) V)
    (hV : Module.finrank k V = 2) (hchar : (2 : k) ≠ 0) (hirr : ρ.IsIrreducible)
    (hres : ¬ Representation.IsIrreducible (ρ.comp (character p).ker.subtype)) :
    ∃ χ : Field.absoluteGaloisGroup ℚ →* kˣ,
      χ ≠ 1 ∧ (∀ g : (character p).ker, χ g = 1) ∧ (∀ g, χ g ^ 2 = 1) ∧
      (∃ e : V ≃ₗ[k] V, ∀ g, e.conj (ρ g) = (χ g : k) • ρ g) ∧
      ∃ t : localInertiaGroup (LocalCyclotomic.rationalPlace p),
        χ (Field.absoluteGaloisGroup.map
          (algebraMap ℚ ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)) t.1) = -1 := by
  obtain ⟨χ, hχ, hker, hsq, e, he⟩ :=
    ρ.exists_quadratic_selfTwist (character p).ker hV hchar hirr hres
  obtain ⟨t, ht⟩ := exists_inertia_detector (k := k) p
  exact ⟨χ, hχ, hker, hsq, ⟨e, he⟩, t, ht χ hχ hker hsq⟩

end CyclotomicQuadratic

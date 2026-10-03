/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.CyclotomicQuadraticDetection
public import FLT.Deformations.RepresentationTheory.Irreducible
public import FLT.Slop.RepresentationTheory.OddAbsIrredSlop

/-!
# Separate small-prime cyclotomic branches

For p = 2 the cyclotomic kernel is the full group. For p = 3 the ordinary
cyclotomic-generator trace is zero, so the large-prime trace proof does not apply.
-/

@[expose] public noncomputable section
universe u
namespace CyclotomicQuadratic

/-- The mod-two cyclotomic character is trivial. -/
theorem character_two_eq_one : character 2 = 1 := by
  apply MonoidHom.ext
  intro g
  have h : ∀ c : (ZMod 2)ˣ, c = 1 := by decide
  exact h _

/-- The mod-two cyclotomic kernel is the entire absolute Galois group. -/
theorem character_two_ker : (character 2).ker = ⊤ := by rw [character_two_eq_one]; simp

/-- At p = 2 restriction to the cyclotomic kernel preserves every irreducible representation. -/
theorem irreducible_restriction_two {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (Field.absoluteGaloisGroup ℚ) V) (hirr : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp (character 2).ker.subtype) := by
  obtain ⟨hn, hρ⟩ := (Slop.OddRep.isIrreducible_iff_forall ρ).mp hirr
  apply (Slop.OddRep.isIrreducible_iff_forall _).mpr
  refine ⟨hn, fun W hW ↦ hρ W ?_⟩
  intro g x hx
  exact hW ⟨g, by rw [character_two_ker]; trivial⟩ x hx

/-- The p = 2 full-kernel statement also preserves absolute irreducibility. -/
theorem absolute_restriction_two {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (Field.absoluteGaloisGroup ℚ) V)
    (habs : ρ.IsAbsolutelyIrreducible.{u}) :
    Representation.IsAbsolutelyIrreducible.{u} (ρ.comp (character 2).ker.subtype) := by
  constructor
  intro E _ _
  exact irreducible_restriction_two (Representation.baseChange E ρ)
    (habs.absolutelyIrreducible E inferInstance inferInstance)

/-- At p = 3 an ordinary cyclotomic generator has zero trace in every coefficient extension. -/
theorem ordinary_generator_trace_three {k : Type*} [Field k] [CharP k 3]
    (c : (ZMod 3)ˣ) (hc : orderOf c = 2) :
    (1 : k) + ZMod.castHom (dvd_refl 3) k (c : ZMod 3) = 0 := by
  have hn : c ≠ 1 := by intro h; simp only [h, orderOf_one] at hc; omega
  have hcval : (c : ZMod 3) = -1 := by
    apply (sq_eq_one_iff.mp ?_).resolve_left
    · exact fun h ↦ hn (Units.ext h)
    · exact congrArg Units.val (show c ^ 2 = 1 from hc ▸ pow_orderOf_eq_one c)
  rw [hcval, map_neg, map_one, add_neg_cancel]

end CyclotomicQuadratic

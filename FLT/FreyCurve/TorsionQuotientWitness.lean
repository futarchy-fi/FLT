/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Mazur
import FLT.FreyCurve.Serre.AwayFromP
import FLT.FreyCurve.Serre.FixedLineDescent
import FLT.FreyCurve.Serre.GoodReductionAtPProof
import FLT.FreyCurve.Serre.QuotientCurve
import FLT.FreyCurve.Serre.UnramifiedCharacter

/-!
# Retaining the quotient witness in the reducible Frey argument

The old torsion-configuration existential forgets how its target curve was
obtained. This refinement retains a map from the original rational points
whose kernel is killed by p, and the rational p-torsion on its target.
In the fixed-line case the map is the identity. No assertion that an arbitrary
additive map is an algebraic isogeny is made here.
-/

@[expose] public section

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace FreyPackage

/-- Reducibility gives rational p-torsion on a target with the original kernel control. -/
theorem torsion_quotient_witness_of_reducible (P : FreyPackage) :
    have _instPrime : Fact P.p.Prime := ⟨P.pp⟩
    ¬ GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos) →
      ∃ (E : WeierstrassCurve ℚ), E.IsElliptic ∧
        ∃ (φ : (P.freyCurve⁄ℚ).Point →+ (E⁄ℚ).Point)
          (f : ZMod P.p →+ (E⁄ℚ).Point),
          (∀ x, φ x = 0 → P.p • x = 0) ∧ Function.Injective f := by
  dsimp only
  let : Fact P.p.Prime := ⟨P.pp⟩
  intro hred
  obtain ⟨F⟩ := P.filtration_of_reducible hred
  have haway := P.characters_unramified_away F
  have htriv : (∀ g x, F.χ₁ g x = x) ∨ (∀ g x, F.χ₂ g x = x) := by
    rcases P.one_character_unramified_at_p_of_goodReduction
        (goodReductionAtPQuotient P.p P.pp P.hp5) F with h₁ | h₂
    · left
      apply GaloisRep.trivial_of_everywhere_unramified F.χ₁
      intro q hq
      by_cases heq : q = P.p
      · subst q
        exact h₁
      · exact (haway q hq heq).1
    · right
      apply GaloisRep.trivial_of_everywhere_unramified F.χ₂
      intro q hq
      by_cases heq : q = P.p
      · subst q
        exact h₂
      · exact (haway q hq heq).2
  rcases htriv with h₁ | h₂
  · obtain ⟨f, hf⟩ := rational_torsion_of_fixed_line P.freyCurve P.p
      F.i F.i_injective (fun g x ↦ (F.i_equivariant g x).trans (congrArg F.i (h₁ g x)))
    refine ⟨P.freyCurve, inferInstance, AddMonoidHom.id _, f, ?_, hf⟩
    intro x hx
    change x = 0 at hx
    rw [hx, nsmul_zero]
  · obtain ⟨E, hE, φ, f, hker, hf⟩ :=
      quotient_curve_of_trivial_quotient P.freyCurve P.p P.hppos
        (by have := P.hp5; omega) F.q F.q_surjective
        (fun g v ↦ (F.q_equivariant g v).trans (h₂ g (F.q v)))
    exact ⟨E, hE, φ, f, hker, hf⟩

end FreyPackage

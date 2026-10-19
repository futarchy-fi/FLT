/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.QuotientCurveEquation
public import FLT.FreyCurve.Mazur
import FLT.FreyCurve.Serre.AwayFromP
import FLT.FreyCurve.Serre.FixedLineDescent
import FLT.FreyCurve.Serre.GoodReductionAtPProof
import FLT.FreyCurve.Serre.QuotientCurve
import FLT.FreyCurve.Serre.UnramifiedCharacter

/-!
# Vélu target provenance in the reducible Frey argument

The target is either the original Frey equation or the descended coefficient
curve of a surjective, invariant quotient of its geometric p-torsion.
This retains the curve construction rather than only kernel control on points.
-/

@[expose] public section

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace FreyPackage

/-- The two possible target equations in the reducible Frey construction. -/
def IsVeluTarget (P : FreyPackage) (E : WeierstrassCurve ℚ) : Prop :=
  E = P.freyCurve ∨
    ∃ q : (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p →ₗ[ZMod P.p]
        ZMod P.p,
      Function.Surjective q ∧
      (∀ g t, q (P.freyCurve.torsionGaloisRepresentation P.p g t) = q t) ∧
      Velu.TorsionQuotientEquation P.freyCurve P.p P.hppos q E

/-- Reducibility gives rational p-torsion on an actual descended Vélu target or the source. -/
theorem velu_target_witness_of_reducible (P : FreyPackage) :
    have _instPrime : Fact P.p.Prime := ⟨P.pp⟩
    ¬ GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos) →
      ∃ (E : WeierstrassCurve ℚ), E.IsElliptic ∧ P.IsVeluTarget E ∧
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
    refine ⟨P.freyCurve, inferInstance, Or.inl rfl, AddMonoidHom.id _, f, ?_, hf⟩
    intro x hx
    change x = 0 at hx
    rw [hx, nsmul_zero]
  · have hfixed : ∀ g v, F.q (P.freyCurve.torsionGaloisRepresentation P.p g v) = F.q v :=
      fun g v ↦ (F.q_equivariant g v).trans (h₂ g (F.q v))
    obtain ⟨E, heq, hE, φ, f, hker, hf⟩ :=
      Velu.exists_torsionQuotient_equation_maps P.freyCurve P.p P.hppos F.q
        P.hp_odd F.q_surjective hfixed
    exact ⟨E, hE, Or.inr ⟨F.q, F.q_surjective, hfixed, heq⟩, φ, f, hker, hf⟩

end FreyPackage

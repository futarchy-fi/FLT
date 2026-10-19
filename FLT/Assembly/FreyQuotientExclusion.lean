/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Assembly.FreyIrreducibility
public import FLT.FreyCurve.TorsionQuotientWitness
public import FLT.Mazur.CyclicTorsionPoint
import FLT.FreyCurve.Serre.FreyTwoTorsion
import FLT.FreyCurve.Serre.JoinCoprimeTorsion

/-!
# A torsion exclusion restricted to Frey quotient witnesses

Only targets receiving a rational-point map from an actual Frey curve, with
p-killed kernel, enter this interface. The identity map includes the Frey
curve itself. The condition is weaker than excluding prime torsion on all
rational elliptic curves; it does not identify arbitrary additive maps with
algebraic isogenies.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine

namespace FLT.Assembly

/-- Exclude p-torsion only on the targets allowed by the refined Frey witness. -/
def FreyQuotientTorsionExclusion : Prop :=
  ∀ (P : FreyPackage), 17 ≤ P.p →
    ∀ (E : WeierstrassCurve ℚ), E.IsElliptic →
      ∀ (φ : (P.freyCurve⁄ℚ).Point →+ (E⁄ℚ).Point),
        (∀ x, φ x = 0 → P.p • x = 0) →
        ¬ ∃ f : ZMod P.p →+ (E⁄ℚ).Point, Function.Injective f

/-- The broad torsion exclusion produces the restricted quotient exclusion. -/
theorem freyQuotientTorsionExclusion_of_torsionExclusion
    (hmazur : MazurTorsionExclusion) : FreyQuotientTorsionExclusion := by
  intro P hp17 E hE φ hker hf
  obtain ⟨f, hf⟩ := hf
  obtain ⟨f₂, hf₂⟩ := P.frey_full_two_torsion
  have hcoprime : Nat.Coprime 2 P.p := Nat.coprime_two_left.mpr P.hp_odd
  obtain ⟨g₂, hg₂⟩ := fullTwoTorsion_survives_of_kernel_killed hcoprime f₂ hf₂ φ hker
  exact hmazur P.p P.pp hp17 E hE
    (SerrePlan.join_coprime_torsion hcoprime g₂ hg₂ f hf)

/-- The restricted quotient exclusion supplies exactly the Frey irreducibility input. -/
theorem freyIrreducibility_of_quotientTorsionExclusion
    (h : FreyQuotientTorsionExclusion) : FreyIrreducibility := by
  intro P hp17
  by_contra hred
  obtain ⟨E, hE, φ, f, hker, hf⟩ := P.torsion_quotient_witness_of_reducible hred
  exact h P hp17 E hE φ hker ⟨f, hf⟩

/-- The restricted torsion input can equivalently be stated using points of exact order p. -/
theorem freyQuotientTorsionExclusion_iff_no_points :
    FreyQuotientTorsionExclusion ↔
      ∀ (P : FreyPackage), 17 ≤ P.p →
        ∀ (E : WeierstrassCurve ℚ), E.IsElliptic →
          ∀ (φ : (P.freyCurve⁄ℚ).Point →+ (E⁄ℚ).Point),
            (∀ x, φ x = 0 → P.p • x = 0) →
            ¬ ∃ Q : (E⁄ℚ).Point, addOrderOf Q = P.p := by
  constructor
  · intro h P hp17 E hE φ hker hQ
    exact h P hp17 E hE φ hker ((FLT.Mazur.cyclic_embedding_iff_point P.p).mpr hQ)
  · intro h P hp17 E hE φ hker hf
    exact h P hp17 E hE φ hker ((FLT.Mazur.cyclic_embedding_iff_point P.p).mp hf)

end FLT.Assembly

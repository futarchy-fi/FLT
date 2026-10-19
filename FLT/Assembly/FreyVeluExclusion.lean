/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Assembly.FreyQuotientExclusion
public import FLT.Assembly.NarrowFreyFinal
public import FLT.FreyCurve.VeluTargetTwoTorsion

/-!
# The torsion exclusion on actual descended Vélu equations

The input refers only to the two target equations constructed from a Frey
package. Ellipticity, the rational map, and full two-torsion are derived.
The exclusion itself remains the arithmetic theorem to be proved.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine

namespace FLT.Assembly

/-- No rational p-torsion on the source or a descended Vélu target of a Frey package. -/
def FreyVeluTorsionExclusion : Prop :=
  ∀ (P : FreyPackage), 17 ≤ P.p →
    ∀ (E : WeierstrassCurve ℚ), P.IsVeluTarget E →
      ¬ ∃ f : ZMod P.p →+ (E⁄ℚ).Point, Function.Injective f

/-- The older additive-map exclusion supplies the equation-restricted input. -/
theorem freyVeluTorsionExclusion_of_quotientExclusion
    (h : FreyQuotientTorsionExclusion) : FreyVeluTorsionExclusion := by
  intro P hp17 E hE
  obtain ⟨φ, hφ⟩ := hE.exists_rational_map
  exact h P hp17 E hE.isElliptic φ hφ

/-- The universal torsion exclusion supplies the actual-target input using proved two-torsion. -/
theorem freyVeluTorsionExclusion_of_torsionExclusion
    (h : MazurTorsionExclusion) : FreyVeluTorsionExclusion := by
  intro P hp17 E hE hf
  obtain ⟨f, hf⟩ := hf
  obtain ⟨f₂, hf₂⟩ := hE.full_two_torsion
  exact h P.p P.pp hp17 E hE.isElliptic
    (SerrePlan.join_coprime_torsion (Nat.coprime_two_left.mpr P.hp_odd) f₂ hf₂ f hf)

/-- Excluding torsion on the retained equations suffices for Frey irreducibility. -/
theorem freyIrreducibility_of_veluTorsionExclusion
    (h : FreyVeluTorsionExclusion) : FreyIrreducibility := by
  intro P hp17
  by_contra hred
  obtain ⟨E, _, hE, _, f, _, hf⟩ := P.velu_target_witness_of_reducible hred
  exact h P hp17 E hE ⟨f, hf⟩

/-- The equation-restricted input is equivalent to excluding exact-order p points. -/
theorem freyVeluTorsionExclusion_iff_no_points :
    FreyVeluTorsionExclusion ↔
      ∀ (P : FreyPackage), 17 ≤ P.p →
        ∀ (E : WeierstrassCurve ℚ), P.IsVeluTarget E →
          ¬ ∃ Q : (E⁄ℚ).Point, addOrderOf Q = P.p := by
  constructor
  · intro h P hp17 E hE hQ
    exact h P hp17 E hE ((FLT.Mazur.cyclic_embedding_iff_point P.p).mpr hQ)
  · intro h P hp17 E hE hf
    exact h P hp17 E hE ((FLT.Mazur.cyclic_embedding_iff_point P.p).mp hf)

/-- Conditional positive-natural FLT using only the constructed-target torsion exclusion. -/
theorem pow_add_pow_ne_pow_of_veluTorsionExclusion (h : FreyVeluTorsionExclusion)
    (hred : FLT.Bosses.B4) (x y z : ℕ+) (n : ℕ) (hn : n > 2) :
    x ^ n + y ^ n ≠ z ^ n :=
  pow_add_pow_ne_pow_of_freyIrreducibility
    (freyIrreducibility_of_veluTorsionExclusion h) hred x y z n hn

end FLT.Assembly

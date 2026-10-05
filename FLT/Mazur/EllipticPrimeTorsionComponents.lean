/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticMinimalAdditiveComponents
public import FLT.Mazur.EllipticNonsplitNodeComponents

/-!
# Prime torsion in the identity component

A prime larger than a finite component quotient cannot annihilate a
nonzero component class. The proved additive and nonsplit nodal bounds
therefore force the corresponding prime torsion into actual smooth reduction.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- Prime torsion reduces smoothly when the component quotient has smaller finite order. -/
theorem smoothReduction_prime_torsion_of_component_bound
    [Finite (EllipticComponentQuotient A W)] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (EllipticComponentQuotient A W) < p)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : p • P = 0) :
    SmoothReduction A W P := by
  apply (ellipticComponentHom_eq_zero A W P).mp
  let c := ellipticComponentHom A W P
  have hc : p • c = 0 := by simp only [c, ← map_nsmul, hP, map_zero]
  have hd : addOrderOf c ∣ p := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hc
  rcases hp.eq_one_or_self_of_dvd _ hd with h1 | he
  · have h := addOrderOf_nsmul_eq_zero c
    simpa only [h1, one_nsmul] using h
  · have hb := Nat.le_of_dvd (Nat.card_pos (α := EllipticComponentQuotient A W))
      (he ▸ addOrderOf_dvd_natCard c)
    omega

variable [IsDiscreteValuationRing A] [PerfectField (ResidueField A)]
  [(W.map (algebraMap A K)).IsElliptic]

/-- On a minimal additive equation, prime torsion of order greater than four lies in E₀. -/
theorem smoothReduction_prime_torsion_minimalAdditive
    [IsMinimal A (W.map (algebraMap A K))]
    (hΔ : W.Δ ∈ maximalIdeal A) (hc : W.c₄ ∈ maximalIdeal A)
    {p : ℕ} (hp : p.Prime) (hp4 : 4 < p)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : p • P = 0) :
    SmoothReduction A W P := by
  obtain ⟨hf, hb⟩ := minimalAdditive_components A W hΔ hc
  let := hf
  exact smoothReduction_prime_torsion_of_component_bound A W hp (lt_of_le_of_lt hb hp4) P hP

/-- On a nonsplit nodal equation, every odd-prime torsion point lies in E₀. -/
theorem smoothReduction_prime_torsion_nonsplitNodal
    (hΔ : W.Δ ∈ maximalIdeal A) (hc : IsUnit W.c₄)
    (hns : ¬ (W.nodePoly.map (residue A)).Splits)
    {p : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : p • P = 0) :
    SmoothReduction A W P := by
  obtain ⟨hf, _, hb⟩ := nonsplitNodal_components A W hΔ hc hns
  let := hf
  exact smoothReduction_prime_torsion_of_component_bound A W hp (lt_of_le_of_lt hb hp2) P hP

end FLT.Mazur

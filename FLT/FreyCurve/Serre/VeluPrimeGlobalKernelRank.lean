/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGlobalDegree
public import FLT.FreyCurve.Serre.VeluPrimeKernel

/-!
# The full original prime-torsion quotient kernel has length p

The general exact-fiber computation applies to the original torsionKernel
on the original source over the algebraic closure of the rationals.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q) [Fintype (torsionKernel E p q)] (hp : Odd p)

local notation "EQ" => E.map (algebraMap ℚ (AlgebraicClosure ℚ))
local notation "GQ" => torsionKernel E p q
/-- The original finite subgroup instance, cached in the mapped-cubic presentation. -/
local instance primeRankFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  inferInstanceAs (Fintype (torsionKernel E p q))

local notation "φ" => veluGlobalMorphism EQ GQ (torsionKernel_ne_neg E p q hp)

include hq

/-- The full actual kernel contains exactly p scheme points. -/
theorem primeGlobalKernel_card :
    Nat.card (veluGlobalKernel EQ GQ (torsionKernel_ne_neg E p q hp)) = p := by
  rw [veluGlobalKernel_card]
  exact torsionKernel_card_prime E p q hq

/-- The original full scheme-theoretic kernel has algebraic length p. -/
theorem primeGlobalKernel_length :
    FLT.Mazur.FCurve.finiteSchemeLength (pullback.snd φ (integralCurveZero (curve EQ GQ))) =
      p := by
  rw [veluGlobalKernel_length]
  exact torsionKernel_card_prime E p q hq

/-- The actual full kernel has finite flat rank p over the original algebraic closure. -/
theorem primeGlobalKernel_rank (s : Spec (.of (AlgebraicClosure ℚ))) :
    (pullback.snd φ (integralCurveZero (curve EQ GQ))).finrank s = p := by
  rw [veluGlobalKernel_rank]
  exact torsionKernel_card_prime E p q hq

/-- The original global map itself has rank p at every point of its actual target. -/
theorem primeGlobalMorphism_rank (y : integralCurve (curve EQ GQ)) : (φ).finrank y = p := by
  rw [veluGlobalMorphism_rank]
  exact torsionKernel_card_prime E p q hq

/-- The original global prime quotient morphism is finite locally free of degree p. -/
theorem primeGlobalMorphism_degree : FLT.Mazur.FCurve.FiniteLocallyFreeDegree φ p := by
  exact ⟨inferInstance, inferInstance, inferInstance, primeGlobalMorphism_rank E p q hq hp⟩

end WeierstrassCurve.Velu

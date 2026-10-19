/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticComponentQuotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Specified cyclic torsion maps in the component quotient

For a prime cyclic parameter group, a generator outside smooth reduction
makes the exact composite to the rational component quotient injective.
This preserves the parameterization of the subgroup under local transport.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (p : ℕ) [Fact p.Prime]
  (f : ZMod p →+ (W.map (algebraMap A K)).toProjective.Point)

/-- A nonsmooth cyclic generator embeds its entire specified prime subgroup in components. -/
theorem cyclicComponentHom_injective (h : ¬ SmoothReduction A W (f 1)) :
    Function.Injective ((ellipticComponentHom A W).comp f) := by
  let g := (ellipticComponentHom A W).comp f
  let _ : Fact (Nat.card (ZMod p)).Prime := ⟨by simpa using (Fact.out : p.Prime)⟩
  rcases g.ker.eq_bot_or_eq_top_of_prime_card with hb | ht
  · exact g.ker_eq_bot_iff.mp hb
  · exfalso
    apply h
    apply (ellipticComponentHom_eq_zero A W (f 1)).mp
    have hm : (1 : ZMod p) ∈ g.ker := ht ▸ AddSubgroup.mem_top _
    exact hm

/-- In the transported subgroup, smooth reduction is exactly the zero parameter. -/
theorem cyclic_smoothReduction_iff (h : ¬ SmoothReduction A W (f 1)) (a : ZMod p) :
    SmoothReduction A W (f a) ↔ a = 0 := by
  rw [← ellipticComponentHom_eq_zero]
  exact (cyclicComponentHom_injective A W p f h).eq_iff' (map_zero _)

/-- The actual component class of the transported generator has the original prime order. -/
theorem cyclicComponentHom_addOrderOf (h : ¬ SmoothReduction A W (f 1)) :
    addOrderOf (ellipticComponentHom A W (f 1)) = p :=
  (addOrderOf_injective ((ellipticComponentHom A W).comp f)
    (cyclicComponentHom_injective A W p f h) 1).trans (ZMod.addOrderOf_one p)

end FLT.Mazur

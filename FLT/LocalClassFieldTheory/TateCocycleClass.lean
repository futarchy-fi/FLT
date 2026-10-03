/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Cocycle representatives in the actual Tate complex

The same cycle-class constructor and boundary formula work in every integer
degree, including across the norm differential in degrees minus one and zero.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory HomologicalComplex

variable {k G : Type} [CommRing k] [Group G] [Fintype G]

/-- The class of an actual Tate cocycle, in any integer degree. -/
def tateCocycleClass (M : Rep k G) (n : ℤ) (z : (tateComplex M).X n)
    (hz : (tateComplex M).d n (n + 1) z = 0) : tateCohomology M n :=
  (tateComplex M).homologyπ n ((tateComplex M).cyclesMk z (n + 1) (by simp) hz)

/-- Every Tate class has a representative in the actual Tate complex. -/
theorem tateCocycleClass_surjective (M : Rep k G) (n : ℤ) (a : tateCohomology M n) :
    ∃ z hz, tateCocycleClass M n z hz = a := by
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective ((tateComplex M).homologyπ n)).mp
    inferInstance a
  have hz : (tateComplex M).d n (n + 1) ((tateComplex M).iCycles n y) = 0 :=
    congrArg (fun f => f.hom y) ((tateComplex M).iCycles_d n (n + 1))
  refine ⟨(tateComplex M).iCycles n y, hz, congrArg ((tateComplex M).homologyπ n) ?_⟩
  apply (ModuleCat.mono_iff_injective ((tateComplex M).iCycles n)).mp inferInstance
  exact (tateComplex M).i_cyclesMk _ _ _ _

/-- A lifted differential is a cycle in the left-hand Tate complex. -/
theorem tateConnecting_cycle {S : ShortComplex (Rep k G)} (hS : S.ShortExact) (n : ℤ)
    (y : (tateComplex S.X₂).X n) (x : (tateComplex S.X₁).X (n + 1))
    (hx : (tateComplex.map S.f).f (n + 1) x = (tateComplex S.X₂).d n (n + 1) y) :
    (tateComplex S.X₁).d (n + 1) (n + 1 + 1) x = 0 :=
  (TateCohomology.map_tateComplexFunctor_shortExact hS).d_eq_zero_of_f_eq_d_apply
    n (n + 1) y x hx (n + 1 + 1)

/-- The Tate connecting map is computed by lifting and differentiating representatives. -/
theorem tateConnecting_apply {S : ShortComplex (Rep k G)} (hS : S.ShortExact) (n : ℤ)
    (z : (tateComplex S.X₃).X n) (hz : (tateComplex S.X₃).d n (n + 1) z = 0)
    (y : (tateComplex S.X₂).X n) (hy : (tateComplex.map S.g).f n y = z)
    (x : (tateComplex S.X₁).X (n + 1))
    (hx : (tateComplex.map S.f).f (n + 1) x = (tateComplex S.X₂).d n (n + 1) y) :
    TateCohomology.δ hS n (tateCocycleClass S.X₃ n z hz) =
      tateCocycleClass S.X₁ (n + 1) x (tateConnecting_cycle hS n y x hx) :=
  (TateCohomology.map_tateComplexFunctor_shortExact hS).δ_apply
    n (n + 1) rfl z hz y hy x hx (n + 1 + 1) (by simp)

end LocalClassFieldTheory

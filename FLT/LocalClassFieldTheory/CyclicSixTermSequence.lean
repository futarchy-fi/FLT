/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CyclicPeriodicExact
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# The cyclic six-term exact sequence

For a short exact coefficient sequence A → B → C, the two periodic
homologies form the exact cycle A⁰ → B⁰ → C⁰ → A¹ → B¹ → C¹ → A⁰.
Both connecting maps are constructed by the snake lemma. Boolean parity
makes the return to even degree literal, with no assumed periodicity map.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory

variable {k G : Type} [CommRing k] [CommGroup G] [Fintype G]
  (S : ShortComplex (Rep k G)) (g : G) (hS : S.ShortExact)

/-- The two coefficient maps have zero composite on periodic homology. -/
theorem cyclicPeriodicHomology_comp (i : Bool) :
    cyclicPeriodicHomologyMap g S.f i ≫ cyclicPeriodicHomologyMap g S.g i = 0 := by
  change HomologicalComplex.homologyMap (cyclicPeriodicSequence S g).f i ≫
    HomologicalComplex.homologyMap (cyclicPeriodicSequence S g).g i = 0
  rw [← HomologicalComplex.homologyMap_comp, (cyclicPeriodicSequence S g).zero,
    HomologicalComplex.homologyMap_zero]

/-- Each connecting map is killed by the next coefficient map. -/
theorem cyclicPeriodicConnecting_comp (i : Bool) :
    cyclicPeriodicConnecting S g hS i ≫ cyclicPeriodicHomologyMap g S.f (!i) = 0 :=
  (cyclicPeriodicSequence_shortExact S g hS).δ_comp i (!i) rfl

/-- Each connecting map kills the preceding coefficient map. -/
theorem cyclicPeriodicHomology_comp_connecting (i : Bool) :
    cyclicPeriodicHomologyMap g S.g i ≫ cyclicPeriodicConnecting S g hS i = 0 :=
  (cyclicPeriodicSequence_shortExact S g hS).comp_δ i (!i) rfl

/-- Exactness at A in the parity following the connecting map. -/
theorem cyclicSixTerm_exact_left (i : Bool) :
    (ShortComplex.mk _ _ (cyclicPeriodicConnecting_comp S g hS i)).Exact :=
  (cyclicPeriodicSequence_shortExact S g hS).homology_exact₁ i (!i) rfl

include hS in
/-- Exactness at B in either parity. -/
theorem cyclicSixTerm_exact_middle (i : Bool) :
    (ShortComplex.mk _ _ (cyclicPeriodicHomology_comp S g i)).Exact :=
  (cyclicPeriodicSequence_shortExact S g hS).homology_exact₂ i

/-- Exactness at C in either parity. -/
theorem cyclicSixTerm_exact_right (i : Bool) :
    (ShortComplex.mk _ _ (cyclicPeriodicHomology_comp_connecting S g hS i)).Exact :=
  (cyclicPeriodicSequence_shortExact S g hS).homology_exact₃ i (!i) rfl

/-- All six exactness assertions, including both ends of the cycle. -/
theorem cyclicSixTerm_exact : ∀ i : Bool,
    (ShortComplex.mk _ _ (cyclicPeriodicConnecting_comp S g hS i)).Exact ∧
    (ShortComplex.mk _ _ (cyclicPeriodicHomology_comp S g i)).Exact ∧
    (ShortComplex.mk _ _ (cyclicPeriodicHomology_comp_connecting S g hS i)).Exact :=
  fun i => ⟨cyclicSixTerm_exact_left S g hS i, cyclicSixTerm_exact_middle S g hS i,
    cyclicSixTerm_exact_right S g hS i⟩

/-- The connecting maps commute with morphisms of coefficient short exact sequences. -/
theorem cyclicPeriodicConnecting_naturality {T : ShortComplex (Rep k G)}
    (hT : T.ShortExact) (φ : S ⟶ T) (i : Bool) :
    cyclicPeriodicConnecting S g hS i ≫ cyclicPeriodicHomologyMap g φ.τ₁ (!i) =
      cyclicPeriodicHomologyMap g φ.τ₃ i ≫ cyclicPeriodicConnecting T g hT i :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((cyclicPeriodicFunctor g).mapShortComplex.map φ)
    (cyclicPeriodicSequence_shortExact S g hS)
    (cyclicPeriodicSequence_shortExact T g hT) i (!i) rfl

end LocalClassFieldTheory

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CyclicPeriodicHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# Exact coefficient sequences give exact periodic complexes

Short exactness of the coefficient sequence is the input. Short exactness of
its two-periodic complexes is proved degreewise, without a cohomological premise.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory

variable {k G : Type} [CommRing k] [CommGroup G] [Fintype G]
  (S : ShortComplex (Rep k G)) (g : G)

/-- Apply the actual periodic complex functor to the coefficient sequence. -/
def cyclicPeriodicSequence :
    ShortComplex (HomologicalComplex (ModuleCat k) cyclicPeriodicShape) :=
  S.map (cyclicPeriodicFunctor g)

/-- Exactness of the periodic complexes follows from coefficient short exactness. -/
theorem cyclicPeriodicSequence_shortExact (hS : S.ShortExact) :
    (cyclicPeriodicSequence S g).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  have := hS.mono_f
  have := hS.epi_g
  exact hS.map (forget₂ (Rep k G) (ModuleCat k))

/-- The connecting map changes parity, including the odd-to-even wrap. -/
def cyclicPeriodicConnecting (hS : S.ShortExact) (i : Bool) :
    (cyclicPeriodicComplex S.X₃ g).homology i ⟶
      (cyclicPeriodicComplex S.X₁ g).homology (!i) :=
  (cyclicPeriodicSequence_shortExact S g hS).δ i (!i) rfl

/-- The coefficient maps induce maps on either periodic homology. -/
def cyclicPeriodicHomologyMap {A B : Rep k G} (f : A ⟶ B) (i : Bool) :
    (cyclicPeriodicComplex A g).homology i ⟶ (cyclicPeriodicComplex B g).homology i :=
  HomologicalComplex.homologyMap (cyclicPeriodicMap f g) i

end LocalClassFieldTheory

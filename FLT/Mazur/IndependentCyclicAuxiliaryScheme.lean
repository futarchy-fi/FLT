/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryLevel

/-!
# Independent auxiliary and cyclic markings

The product of the two faithful marking schemes allows their images to
intersect. In particular it imposes no coprimality between four and the cyclic
order. Both markings still consist of universally distinct sections.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
open AuxiliaryLevel
variable (n : ℕ) [NeZero n]

/-- Auxiliary and cyclic markings are each faithful, independently of each other. -/
def independentCyclicAuxiliaryScheme : Over parameterBase :=
  Limits.prod levelFour (faithfulScheme universalGroup (Multiplicative (ZMod n)))

/-- Forget just the cyclic marking, retaining the original auxiliary parameter. -/
def independentCyclicAuxiliary : independentCyclicAuxiliaryScheme n ⟶ levelFour :=
  Limits.prod.fst

/-- Forget just the auxiliary marking, retaining every original cyclic label. -/
def independentCyclicParameter : independentCyclicAuxiliaryScheme n ⟶
    faithfulScheme universalGroup (Multiplicative (ZMod n)) := Limits.prod.snd

/-- Any pair of faithful markings over the same coefficients defines an actual chart point. -/
def independentCyclicLift {U : Over parameterBase} (a : U ⟶ levelFour)
    (c : U ⟶ faithfulScheme universalGroup (Multiplicative (ZMod n))) :
    U ⟶ independentCyclicAuxiliaryScheme n := Limits.prod.lift a c

/-- The chart retains the given auxiliary marking exactly. -/
@[reassoc] theorem independentCyclicLift_auxiliary {U : Over parameterBase}
    (a : U ⟶ levelFour)
    (c : U ⟶ faithfulScheme universalGroup (Multiplicative (ZMod n))) :
    independentCyclicLift n a c ≫ independentCyclicAuxiliary n = a :=
  Limits.prod.lift_fst _ _

/-- The chart retains the given cyclic marking exactly, including at even orders. -/
@[reassoc] theorem independentCyclicLift_cyclic {U : Over parameterBase}
    (a : U ⟶ levelFour)
    (c : U ⟶ faithfulScheme universalGroup (Multiplicative (ZMod n))) :
    independentCyclicLift n a c ≫ independentCyclicParameter n = c :=
  Limits.prod.lift_snd _ _

/-- The two actual markings determine the chart point. -/
theorem independentCyclic_hom_ext {U : Over parameterBase}
    (f g : U ⟶ independentCyclicAuxiliaryScheme n)
    (ha : f ≫ independentCyclicAuxiliary n = g ≫ independentCyclicAuxiliary n)
    (hc : f ≫ independentCyclicParameter n = g ≫ independentCyclicParameter n) : f = g :=
  Limits.prod.hom_ext ha hc

end FLT.Mazur.UniversalWeierstrass

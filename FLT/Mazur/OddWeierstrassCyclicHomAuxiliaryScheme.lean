/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryEtale

/-!
# Odd-chart Auxiliary parameters with arbitrary cyclic homomorphisms

Keep the faithful auxiliary level-three marking, but allow collisions in the
cyclic factor. This ambient scheme precedes the subgroup equations: a point
alone is not asserted to define a subgroup of rank n.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open AuxiliaryLevel
variable (n : ℕ) [NeZero n]

/-- Independent auxiliary labels together with an arbitrary cyclic homomorphism. -/
def cyclicHomAuxiliaryScheme : Over parameterBase :=
  Limits.prod levelThree (homScheme universalGroup (Multiplicative (ZMod n)))

/-- Retain the faithful auxiliary marking. -/
def cyclicHomAuxiliary : cyclicHomAuxiliaryScheme n ⟶ levelThree := Limits.prod.fst

/-- Retain every cyclic label, including coincident sections. -/
def cyclicHomParameter : cyclicHomAuxiliaryScheme n ⟶
    homScheme universalGroup (Multiplicative (ZMod n)) := Limits.prod.snd

/-- Pair actual auxiliary and cyclic parameters over the same coefficients. -/
def cyclicHomLift {U : Over parameterBase} (a : U ⟶ levelThree)
    (c : U ⟶ homScheme universalGroup (Multiplicative (ZMod n))) :
    U ⟶ cyclicHomAuxiliaryScheme n := Limits.prod.lift a c

/-- Pairing retains the original auxiliary parameter. -/
@[reassoc] theorem cyclicHomLift_auxiliary {U : Over parameterBase} (a : U ⟶ levelThree)
    (c : U ⟶ homScheme universalGroup (Multiplicative (ZMod n))) :
    cyclicHomLift n a c ≫ cyclicHomAuxiliary n = a := Limits.prod.lift_fst _ _

/-- Pairing retains the original cyclic homomorphism. -/
@[reassoc] theorem cyclicHomLift_cyclic {U : Over parameterBase} (a : U ⟶ levelThree)
    (c : U ⟶ homScheme universalGroup (Multiplicative (ZMod n))) :
    cyclicHomLift n a c ≫ cyclicHomParameter n = c := Limits.prod.lift_snd _ _

/-- Auxiliary and cyclic coordinates determine every ambient parameter. -/
theorem cyclicHom_hom_ext {U : Over parameterBase} (f g : U ⟶ cyclicHomAuxiliaryScheme n)
    (ha : f ≫ cyclicHomAuxiliary n = g ≫ cyclicHomAuxiliary n)
    (hc : f ≫ cyclicHomParameter n = g ≫ cyclicHomParameter n) : f = g :=
  Limits.prod.hom_ext ha hc

end FLT.Mazur.OddWeierstrassParameter

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Assembly.Inputs
public import FLT.Assembly.Mazur
public import FLT.GaloisRepresentation.HardlyRamified.Family
public import FLT.GaloisRepresentation.HardlyRamified.Lift

/-!
# The existing arithmetic theorems as assembly inputs

These adapters supply the three remaining premises of the final assembly from
the rational torsion bound, integral lifting, and compatible-family theorems.
-/

@[expose] public section

namespace FLT.Assembly

/-- The rational torsion bound supplies the required torsion exclusion. -/
theorem mazurTorsionExclusion : MazurTorsionExclusion := by
  intro p hp hp17 E hE
  let instElliptic : E.IsElliptic := hE
  exact mazur_W p hp hp17 E

/-- Integral lifting supplies the lifting premise of the assembly. -/
theorem hardlyRamifiedLifting : HardlyRamifiedLifting := by
  intro k _ _ _ _ p hpodd _ _ _ V _ _ _ _ hV ρ hρirred hρ
  exact GaloisRepresentation.IsHardlyRamified.lifts hpodd V hV ρ hρirred hρ

/-- Compatible families supply the domain-valued family premise of the assembly. -/
theorem hardlyRamifiedCompatibleFamilies : HardlyRamifiedCompatibleFamilies := by
  intro p hpodd _ R _ _ _ _ _ _ _ _ _ V _ _ _ _ hV ρ hρ
  exact GaloisRepresentation.IsHardlyRamified.mem_isCompatible hpodd hV hρ

end FLT.Assembly

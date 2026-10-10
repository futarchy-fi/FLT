/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupTorsionScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Properness of the represented torsion equation

The torsion equation is closed in a separated group. When the group is proper,
its actual torsion scheme is therefore proper, including in residue characteristic
dividing the torsion index. No reducedness or smoothness of the kernel is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.GroupTorsionScheme

variable {S : Scheme} (E : Over S) [GrpObj E] (n : ℕ)

/-- The full torsion equation of a proper group is proper over the original base. -/
instance structure_proper [IsProper E.hom] : IsProper (scheme E n).hom := by
  rw [← (inclusion E n).w]
  infer_instance

/-- Properness of the torsion equation persists over every new base. -/
instance baseChange_proper [IsProper E.hom] {T : Scheme} (g : T ⟶ S) :
    IsProper (pullback.snd (scheme E n).hom g) := inferInstance

end FLT.Mazur.GroupTorsionScheme

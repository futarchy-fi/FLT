/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFinitePowerProperties
public import FLT.Mazur.AuxiliaryLevelHomScheme

/-!
# Finite type marking schemes for separated groups

The multiplication relations are closed in a finite power of a separated
group. Thus finite type and quasi-compactness pass to its marking scheme
without assuming properness of the group.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme} (E : Over S) [GrpObj E] [IsSeparated E.hom]
  (A : Type) [Group A] [Fintype A]

/-- Multiplication relations remain closed for a separated, possibly nonproper group. -/
instance homInclusion_closed_of_separated : IsClosedImmersion (homInclusion E A).left := by
  let _ : IsSeparated (∏ᶜ fun _ : A × A => E).hom :=
    SchemeFinitePower.property E (@IsSeparated) inferInstance (A × A)
  exact isClosedImmersion_equalizer_ι_left (productValues E A) (productIndices E A)

/-- The unrestricted marking scheme is separated over the original base. -/
instance homScheme_separated : IsSeparated (homScheme E A).hom := by
  let _ : IsSeparated (markingPower E A).hom :=
    SchemeFinitePower.property E (@IsSeparated) inferInstance A
  rw [← (homInclusion E A).w]
  infer_instance

/-- A finite type separated group has a locally finite type marking scheme. -/
instance homScheme_locallyOfFiniteType_of_separated [LocallyOfFiniteType E.hom] :
    LocallyOfFiniteType (homScheme E A).hom := by
  let _ : LocallyOfFiniteType (markingPower E A).hom :=
    SchemeFinitePower.property E (@LocallyOfFiniteType) inferInstance A
  rw [← (homInclusion E A).w]
  infer_instance

/-- Quasi-compactness passes to the full marking scheme, including colliding labels. -/
instance homScheme_quasiCompact_of_separated [QuasiCompact E.hom] :
    QuasiCompact (homScheme E A).hom := by
  let _ : QuasiCompact (markingPower E A).hom :=
    SchemeFinitePower.property E (@QuasiCompact) inferInstance A
  rw [← (homInclusion E A).w]
  infer_instance

end FLT.Mazur.AuxiliaryLevel

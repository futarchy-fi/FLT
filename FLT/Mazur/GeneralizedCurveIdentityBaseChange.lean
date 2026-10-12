/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveBaseChange
public import FLT.Mazur.GroupSectionBaseChange

/-!
# The original identity under base change

The actual pulled-back marking agrees with the identity supplied by the full
base-changed generalized curve, without replacing its group or inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
open GroupSectionBaseChange
set_option backward.isDefEq.respectTransparency false

variable {S T : Scheme} (E : GeneralizedEllipticCurve S) (g : T ⟶ S)

/-- The pulled-back original identity is the identity of the actual pulled-back DR object. -/
theorem pullSection_identity :
    pullSection g E.identitySection = (E.baseChange g).identitySection := by
  rw [identitySection, section_comp, identitySection, baseChange_inclusion]
  rfl

end FLT.Mazur.GeneralizedEllipticCurve

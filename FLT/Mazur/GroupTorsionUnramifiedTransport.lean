/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupTorsionTransport
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Formal unramifiedness through the original group comparison

The full torsion equalizer inherits formal unramifiedness from an isomorphic
group family. This transports infinitesimal rigidity, including nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GroupTorsionScheme
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (G H : CommGrp (Over S)) (e : G ≅ H) (n : ℕ)
include e

/-- An actual group isomorphism transports formal unramifiedness of full torsion. -/
theorem transport_formallyUnramified [FormallyUnramified (scheme G.X n).hom] :
    FormallyUnramified (scheme H.X n).hom := by
  have : IsIso (transportIso G H e n).inv.left :=
    inferInstanceAs (IsIso ((Over.forget S).map (transportIso G H e n).inv))
  rw [← Over.w (transportIso G H e n).inv]
  exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ _) inferInstance

end FLT.Mazur.GroupTorsionScheme

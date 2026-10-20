/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupTorsionBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Unramified torsion under arbitrary change of base

The canonical equalizer comparison transports infinitesimal rigidity to the
full torsion equation of the original pulled-back group, including nonreduced
bases. The torsion scheme is not replaced by its set of geometric points.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GroupTorsionScheme
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (g : T ⟶ S) (E : Over S) [GrpObj E] (n : ℕ)

/-- The torsion equation of the actual pulled-back group is formally unramified. -/
theorem baseChange_formallyUnramified [FormallyUnramified (scheme E n).hom] :
    FormallyUnramified (scheme ((Over.pullback g).obj E) n).hom := by
  have : FormallyUnramified ((Over.pullback g).obj (scheme E n)).hom :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : IsIso (baseChangeIso g E n).inv.left :=
    inferInstanceAs (IsIso ((Over.forget T).map (baseChangeIso g E n).inv))
  rw [← Over.w (baseChangeIso g E n).inv]
  exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ _) inferInstance

end FLT.Mazur.GroupTorsionScheme

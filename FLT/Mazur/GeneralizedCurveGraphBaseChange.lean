/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveGraphTransport
public import FLT.Mazur.GeneralizedCurvePullbackCoherence

/-!
# Geometric graph rotations survive arbitrary base change

The canonical direct-to-iterated pullback comparison is equivariant.
Transporting its actual components and nonsmooth points proves the rotation
condition for the actual pulled-back action over every geometric base point.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
variable {S T : Scheme} (E : GeneralizedEllipticCurve S) (g : T ⟶ S)

/-- The actual pulled-back action satisfies DR's geometric rotation condition. -/
theorem pullback_rotations :
    letI : LocallyOfFinitePresentation (E.pullbackCurve g).hom :=
      inferInstanceAs (LocallyOfFinitePresentation (pullback.snd E.curve.hom g))
    GeneralizedCurveGraph.GeometricRotations (E.pullbackAction g) := by
  let : LocallyOfFinitePresentation (E.pullbackCurve g).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd E.curve.hom g))
  intro L _ _ h hsing
  let e := E.pullbackCurveCompIso g h
  let d := E.pullbackGroupCompIso g h
  have hi : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have hs : ¬ Smooth (E.pullbackCurve (h ≫ g)).hom := by
    intro hd
    have := hd
    apply hsing
    change Smooth ((Over.pullback h).obj (E.pullbackCurve g)).hom
    rw [← e.inv.w]
    infer_instance
  have hd := E.rotations L (h ≫ g) hs
  let : LocallyOfFinitePresentation (E.pullbackCurve (h ≫ g)).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd E.curve.hom (h ≫ g)))
  let : LocallyOfFinitePresentation ((Over.pullback h).obj (E.pullbackCurve g)).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd (E.pullbackCurve g).hom h))
  exact GeneralizedCurveGraph.rotations_of_iso e d _ _ (E.pullback_comp_action g h) hd

end FLT.Mazur.GeneralizedEllipticCurve

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPullbackFrameCoordinates

/-!
# Named scalar coordinates of pulled line sections

Keep the scalar-valued frame evaluation sealed when specializing to large schemes.
The tensor coordinate factors through this actual line-section evaluation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
  (e : (pullback f).obj L ≅ structureModule X)

/-- The actual pulled line section, evaluated in the supplied frame. -/
irreducible_def pulledLineCoordinate (s : Γ(L, ⊤)) : Γ(X, ⊤) :=
  e.hom.app ⊤ (pullGlobal f L s)

/-- The tensor coordinate retains its first line factor without expanding frame components. -/
theorem pulledFrameCoordinate_cons_line (m : ℕ) (s : Γ(L, ⊤))
    (t : Γ(tensorPower L m, ⊤)) :
    pulledFrameCoordinate f L e (m + 1) (SectionGradedMultiplication.cons L m ⊤ s t) =
      pulledLineCoordinate f L e s * pulledFrameCoordinate f L e m t := by
  rw [pulledLineCoordinate_def]
  exact pulledFrameCoordinate_cons f L e m s t

end FLT.Mazur.FCurve

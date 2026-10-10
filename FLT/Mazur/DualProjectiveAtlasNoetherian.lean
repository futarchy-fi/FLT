/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallyFreeDualProjectiveAtlas
public import FLT.Mazur.ProjectiveChartNoetherian

/-!
# The actual dual projective atlas over a locally Noetherian base

Each finite free chart is a finite-dimensional projective space over a
Noetherian affine ring. Their actual open cover proves local Noetherianness
of the glued atlas, including the case of varying ranks.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.LocallyFreeDualProjectiveAtlas
open FCurve AffineFiniteFreeAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  (M : X.Modules) (hM : LocallyFiniteFree M)

/-- The original glued atlas is locally Noetherian whenever its base is. -/
theorem space_isLocallyNoetherian : IsLocallyNoetherian (space M hM) := by
  apply (isLocallyNoetherian_iff_openCover (cover M hM)).mpr
  intro i
  let _ : IsNoetherianRing Γ(i.val.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top i.val.toScheme⟩
  change IsLocallyNoetherian (ProjectiveSpace.space Γ(i.val.toScheme, ⊤) (coordinates M i))
  infer_instance

end FLT.Mazur.LocallyFreeDualProjectiveAtlas

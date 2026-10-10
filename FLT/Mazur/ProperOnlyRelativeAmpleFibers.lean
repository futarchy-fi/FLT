/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperOnlyAmpleFiberNeighborhood

/-!
# The proper-only fiber criterion for relative ampleness

The ample neighborhoods of individual fibers supply relative closed power
presentations and then relative ampleness. No finite-presentation or
Noetherian hypothesis is imposed on the original proper family.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace FLT.Mazur.FCurve

/-- Near an ample fiber, a proper family's specified line is relatively ample. -/
theorem exists_relativeAmple_neighborhood_proper {X S : Scheme.{0}}
    (f : X ⟶ S) [IsProper f] (s : S) (L : X.Modules) (hL : LocallyFreeRankOne L)
    (hA : AmpleLineBundle ((pullback (f.fiberι s)).obj L)) :
    ∃ W : S.Opens, s ∈ W ∧ IsAffineOpen W ∧
      RelativeAmple (f ∣_ W) (L.restrict (f ⁻¹ᵁ W).ι) := by
  obtain ⟨W, hsW, hW, ha⟩ := exists_ample_neighborhood_proper f s L hL hA
  let _ : IsAffine W.toScheme := hW
  have hb := ha.of_iso ((restrictFunctorIsoPullback (f ⁻¹ᵁ W).ι).app L)
  exact ⟨W, hsW, hW, (hb.relative_of_affine (f ∣_ W)).relativeAmple⟩

/-- Ample residue-fiber restrictions imply relative ampleness for every proper family. -/
theorem relativeAmple_of_ample_fibers_proper {X S : Scheme.{0}}
    (f : X ⟶ S) [IsProper f] (L : X.Modules) (hL : LocallyFreeRankOne L)
    (hA : ∀ s : S, AmpleLineBundle ((pullback (f.fiberι s)).obj L)) :
    RelativeAmple f L := by
  apply relativeAmple_of_base_neighborhoods hL
  intro s
  obtain ⟨W, hsW, _, ha⟩ := exists_relativeAmple_neighborhood_proper f s L hL (hA s)
  exact ⟨W, hsW, ha⟩

end FLT.Mazur.FCurve

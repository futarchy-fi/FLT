/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedPointFiberSectionLifting
public import FLT.Mazur.StalkBaseClosedFiber

/-!
# Lifting from an arbitrary fiber over the base local ring

A proper family over a locally Noetherian base has a Noetherian local model
at every base point. Ampleness of the original fiber gives section lifting
and eventual positive cohomology vanishing on this actual base change.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback

namespace FLT.Mazur.StalkBase

variable {X S : Scheme.{0}} [IsLocallyNoetherian S]
  (f : X ⟶ S) [IsProper f] (s : S) {L : X.Modules}
  (hline : LocallyFreeRankOne L)
  (hL : AmpleLineBundle ((Scheme.Modules.pullback (f.fiberι s)).obj L))

omit [IsLocallyNoetherian S] in
/-- Properness makes the local-ring family separated as an absolute scheme. -/
lemma family_isSeparated : (family f s).IsSeparated := by
  constructor
  rw [← terminal.comp_from (projection f s)]
  infer_instance

include hline hL

/-- At any ample fiber, large powers lift all closed-fiber sections over the actual local ring. -/
theorem closedFiber_sections_uniform_surjective :
    ∃ N : ℕ, ∀ m ≥ N,
      Function.Surjective
        (pullGlobal ((projection f s).fiberι (IsLocalRing.closedPoint (S.presheaf.stalk s)))
          (tensorPower ((Scheme.Modules.pullback (toSource f s)).obj L) m)) := by
  let _ := family_isSeparated f s
  let R := S.presheaf.stalk s
  let _ : (IsLocalRing.closedPoint R).asIdeal.IsMaximal :=
    inferInstanceAs (IsLocalRing.maximalIdeal R).IsMaximal
  exact BaseAdicCohomology.fiber_sections_uniform_surjective (projection f s)
    (IsLocalRing.closedPoint R) (hline.pullback (toSource f s))
      ((closedFiber_ample_iff f s L).mpr hL)

/-- High powers on the local-ring family have no positive cohomology. -/
theorem line_uniform_cohomology_vanishing :
    ∃ N : ℕ, ∀ m ≥ N, ∀ q : ℕ,
      Subsingleton (ModuleH (tensorPower ((Scheme.Modules.pullback (toSource f s)).obj L) m)
        (q + 1)) := by
  let _ := family_isSeparated f s
  exact BaseAdicCohomology.line_uniform_cohomology_vanishing_of_closedPoint (projection f s)
    (hline.pullback (toSource f s)) ((closedFiber_ample_iff f s L).mpr hL)

end FLT.Mazur.StalkBase

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineFiniteFreeChart

/-!
# Finite free direct images on arbitrary acyclic tests

An arbitrary test whose fibers are acyclic maps into the model's intrinsic
acyclic open. Affine charts of that open give actual finite free direct images.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve
variable {P X T S : Scheme.{0}} [IsLocallyNoetherian S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)

include h hL in
/-- Fiber acyclicity on a test suffices for its actual direct image to be locally finite free. -/
theorem properLineAcyclicBaseChanged_locallyFiniteFree
    (hV : ∀ t : T, ∀ n, Subsingleton
      (ModuleH ((pullback (q.fiberι t)).obj ((pullback p).obj L)) (n + 1))) :
    LocallyFiniteFree ((pushforward q).obj ((pullback p).obj L)) := by
  let V := properLineGlobalAcyclicOpen f L hL
  have hg (t : T) : g t ∈ V := fun n ↦
    (properLine_fiber_vanishing_iff h L hL t (n + 1)).mp (hV t n)
  let I := {U : S.affineOpens // U.1 ≤ V}
  apply locallyFiniteFree_of_openCover _ (fun U : I ↦ g ⁻¹ᵁ U.1.1)
  · apply eq_top_iff.mpr
    intro t _
    obtain ⟨U, hU, ht, hUV⟩ := exists_isAffineOpen_mem_and_subset (hg t)
    exact Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hUV⟩, ht⟩
  · intro U
    exact properLineFiniteFree_chart h L hL U.1.1 U.1.2
      (fun s hs ↦ U.2 hs) (g ⁻¹ᵁ U.1.1) le_rfl

end FLT.Mazur.LineSectionBaseChange

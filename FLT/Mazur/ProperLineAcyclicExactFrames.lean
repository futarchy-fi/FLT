/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineExactRankChart

/-!
# Exact geometric-rank frames on arbitrary acyclic tests

Acyclicity selects an affine chart of the intrinsic model open. The exact
fiber section dimension then constructs an actual frame on the original test.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
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
/-- Each arbitrary acyclic test has frames with exactly its geometric number of sections. -/
theorem properLineAcyclicBaseChanged_exactRank_frame
    (hV : ∀ t : T, ∀ n, Subsingleton
      (ModuleH ((pullback (q.fiberι t)).obj ((pullback p).obj L)) (n + 1)))
    (t : T) (d : ℕ) (hd : properLineFiberSectionRank q ((pullback p).obj L) t = d) :
    ∃ W : T.Opens, t ∈ W ∧ Nonempty
      (((pushforward q).obj ((pullback p).obj L)).restrict W.ι ≅
        SheafOfModules.free (Fin d)) := by
  have hg : g t ∈ properLineGlobalAcyclicOpen f L hL := fun n ↦
    (properLine_fiber_vanishing_iff h L hL t (n + 1)).mp (hV t n)
  obtain ⟨U, hU, ht, hUV⟩ := exists_isAffineOpen_mem_and_subset hg
  have hd' := (properLineFiberSectionRank_baseChange h L hL t).symm.trans hd
  exact properLineExactRank_chart h L hL U hU (fun s hs ↦ hUV hs)
    (g ⁻¹ᵁ U) le_rfl ⟨t, ht⟩ d hd'

end FLT.Mazur.LineSectionBaseChange

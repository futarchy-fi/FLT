/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineRankOneChartDescent
public import FLT.Mazur.ProperAcyclicRankOneLocus

/-!
# Global direct-image rank one on unrestricted acyclic tests

Descend the affine rank-one criterion along inverse images of affine opens
inside an acyclic base open. The varying line need not be globally acyclic,
and the changed base need not be reduced, affine, or Noetherian.
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
/-- Rank one of the actual direct image is detected on every test mapping into an acyclic open. -/
theorem properLineBaseChanged_rankOne_iff_over_open (V : S.Opens)
    (hV : ∀ s : S, s ∈ V → ∀ n,
      Subsingleton (ModuleH ((pullback (f.fiberι s)).obj L) (n + 1)))
    (hg : ∀ t : T, g t ∈ V) :
    LocallyFreeRankOne ((pushforward q).obj ((pullback p).obj L)) ↔
      ∀ t : T, properLineFiberSectionRank f L (g t) = 1 := by
  constructor
  · intro hN t
    obtain ⟨U, hU, ht, hUV⟩ := exists_isAffineOpen_mem_and_subset (hg t)
    have hc := (properLineRankOne_chart_iff h L hL U hU
      (fun s hs n ↦ hV s (hUV hs) n) (g ⁻¹ᵁ U) le_rfl).mp
        (hN.pullback (g ⁻¹ᵁ U).ι)
    exact hc ⟨t, ht⟩
  · intro hr
    let I := {U : S.affineOpens // U.1 ≤ V}
    apply LocallyFreeRankOne.of_openPullbackCover
      (fun U : I ↦ (g ⁻¹ᵁ U.1.1).toScheme) (fun U : I ↦ (g ⁻¹ᵁ U.1.1).ι)
    · intro t
      obtain ⟨U, hU, ht, hUV⟩ := exists_isAffineOpen_mem_and_subset (hg t)
      exact ⟨⟨⟨U, hU⟩, hUV⟩, ⟨t, ht⟩, rfl⟩
    · intro U
      apply (properLineRankOne_chart_iff h L hL U.1.1 U.1.2
        (fun s hs n ↦ hV s (U.2 hs) n) (g ⁻¹ᵁ U.1.1) le_rfl).mpr
      exact fun t ↦ hr ((g ⁻¹ᵁ U.1.1).ι t)

include h hL in
/-- On a globally acyclic family the intrinsic open tests the actual direct image on all schemes. -/
theorem properLineGlobalRankOne_iff
    (hV : ∀ s : S, ∀ n, Subsingleton (ModuleH ((pullback (f.fiberι s)).obj L) (n + 1))) :
    LocallyFreeRankOne ((pushforward q).obj ((pullback p).obj L)) ↔
      ∀ t : T, g t ∈ properLineGlobalRankOneOpen f L hL hV :=
  properLineBaseChanged_rankOne_iff_over_open h L hL ⊤
    (fun s _ n ↦ hV s n) (fun _ ↦ trivial)

include h hL in
/-- Acyclicity of the changed fibers suffices for the rank-one direct-image criterion. -/
theorem properLineAcyclicBaseChanged_rankOne_iff
    (hV : ∀ t : T, ∀ n, Subsingleton
      (ModuleH ((pullback (q.fiberι t)).obj ((pullback p).obj L)) (n + 1))) :
    LocallyFreeRankOne ((pushforward q).obj ((pullback p).obj L)) ↔
      ∀ t : T, properLineFiberSectionRank q ((pullback p).obj L) t = 1 := by
  have hg (t : T) : g t ∈ properLineGlobalAcyclicOpen f L hL := fun n ↦
    (properLine_fiber_vanishing_iff h L hL t (n + 1)).mp (hV t n)
  rw [properLineBaseChanged_rankOne_iff_over_open h L hL
    (properLineGlobalAcyclicOpen f L hL) (fun _ hs ↦ hs) hg]
  exact forall_congr' fun t ↦
    (congrArg (· = 1) (properLineFiberSectionRank_baseChange h L hL t)).to_iff.symm

end FLT.Mazur.LineSectionBaseChange

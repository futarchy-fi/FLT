/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilySectionCartierChart
public import FLT.Mazur.ProperLineGlobalRankOneCriterion

/-!
# Global Cartier existence on unrestricted acyclic tests

Subordinate affine opens of the original locally Noetherian base cover every
test mapping to an acyclic open. The Cartier property of the original split
section descends across their inverse images with its full zero ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
namespace FLT.Mazur.ProperFamilySectionCartierDescent
open FCurve LineSectionBaseChange ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor twistedSectionPushforwardEquiv
variable {P X T S : Scheme.{0}} [IsLocallyNoetherian S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] [GeometricallyIntegral f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  {B : T.Modules} (hB : LocallyFreeRankOne B)
  (s : Γ(tensor ((pullback p).obj L) ((pullback q).obj B), ⊤))
  (hs : SplitLineAffineNeighborhood.LocallySplit
    (twistedSectionPushforwardEquiv q ((pullback p).obj L) hB s))

include h hs in
/-- Acyclicity only on the target open constructs regularity and the full flat zero divisor. -/
theorem regular_and_relativeCartier_over_open (V : S.Opens)
    (hV : ∀ x : S, x ∈ V → ∀ n,
      Subsingleton (ModuleH ((pullback (f.fiberι x)).obj L) (n + 1)))
    (hg : ∀ t : T, g t ∈ V) :
    Mono (globalSectionHom _ s) ∧ RelativeEffectiveCartier q
      (lineSectionZeroIdeal ((hL.pullback p).tensor (hB.pullback q)) s) := by
  let I := {U : S.affineOpens // U.1 ≤ V}
  let W : I → T.Opens := fun U ↦ g ⁻¹ᵁ U.1.1
  have hW : iSup W = ⊤ := by
    apply top_unique
    intro t _
    obtain ⟨U, hU, ht, hUV⟩ := exists_isAffineOpen_mem_and_subset (hg t)
    exact Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hUV⟩, ht⟩
  apply SectionCartierOpenDescent.relativeCartier_of_cover q
    ((hL.pullback p).tensor (hB.pullback q)) s (fun i ↦ q ⁻¹ᵁ W i)
      (q.iSup_preimage_eq_top hW)
  intro U
  have hc := ProperFamilySectionCartierChart.regular_and_relativeCartier
    h L hL U.1.1 U.1.2 (fun x hx n ↦ hV x (U.2 hx) n) (W U) le_rfl hB s hs
  refine ⟨hc.1, hc.2.1, ?_⟩
  have := hc.2.2
  rw [← morphismRestrict_ι q (W U), ← Category.assoc]
  infer_instance

include h hs in
/-- Vanishing on the changed fibers suffices, without any condition on the test scheme. -/
theorem regular_and_relativeCartier
    (hV : ∀ t : T, ∀ n, Subsingleton
      (ModuleH ((pullback (q.fiberι t)).obj ((pullback p).obj L)) (n + 1))) :
    Mono (globalSectionHom _ s) ∧ RelativeEffectiveCartier q
      (lineSectionZeroIdeal ((hL.pullback p).tensor (hB.pullback q)) s) := by
  apply regular_and_relativeCartier_over_open h L hL hB s hs
    (properLineGlobalAcyclicOpen f L hL) (fun _ hx ↦ hx)
  exact fun t n ↦ (properLine_fiber_vanishing_iff h L hL t (n + 1)).mp (hV t n)

end FLT.Mazur.ProperFamilySectionCartierDescent

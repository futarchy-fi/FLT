/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineAcyclicTestChart
public import FLT.Mazur.RelativeSerreAffineAcyclic

/-!
# Vanishing of higher direct images on arbitrary acyclic tests

The affine test opens mapping into affine acyclic model charts form a basis.
Their actual cohomology vanishes, so the positive module higher direct images
vanish over unrestricted test bases.
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
/-- Fiber acyclicity kills every positive actual higher direct image on an arbitrary test. -/
theorem properLineAcyclicBaseChanged_higherImage
    (hV : ∀ t : T, ∀ n, Subsingleton
      (ModuleH ((pullback (q.fiberι t)).obj ((pullback p).obj L)) (n + 1))) :
    ModulePushforwardAcyclic q ((pullback p).obj L) := by
  let V := properLineGlobalAcyclicOpen f L hL
  have hg (t : T) : g t ∈ V := fun n ↦
    (properLine_fiber_vanishing_iff h L hL t (n + 1)).mp (hV t n)
  let B : Set T.Opens := {W | IsAffineOpen W ∧
    ∃ U : S.affineOpens, U.1 ≤ V ∧ W ≤ g ⁻¹ᵁ U.1}
  have hB : Opens.IsBasis B := by
    rw [Opens.isBasis_iff_nbhd]
    intro W t ht
    obtain ⟨U, hU, htu, hUV⟩ := exists_isAffineOpen_mem_and_subset (hg t)
    obtain ⟨Z, hZ, htz, hZW⟩ := exists_isAffineOpen_mem_and_subset
      (show t ∈ W ⊓ g ⁻¹ᵁ U from ⟨ht, htu⟩)
    exact ⟨Z, ⟨hZ, ⟨⟨U, hU⟩, hUV, hZW.trans inf_le_right⟩⟩,
      htz, hZW.trans inf_le_left⟩
  apply ProjectiveSpace.modulePushforwardAcyclic_of_basis q _ hB
  rintro W ⟨hW, U, hUV, hWU⟩ n
  let _ : IsAffine W.toScheme := hW
  exact properLineAcyclic_chart h L hL U.1 U.2 (fun s hs ↦ hUV hs) W hWU n

end FLT.Mazur.LineSectionBaseChange

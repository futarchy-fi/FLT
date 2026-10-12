/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineBundleRestrict
public import FLT.Mazur.ModuleLineBundlePullback

/-!
# Affine neighborhoods carrying actual line frames

Local rank one gives a frame on an affine neighborhood inside any prescribed
open. The frame is obtained by restricting the original trivialization.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme} {M : S.Modules}

/-- An actual line frame restricts to every smaller open neighborhood. -/
def lineFrameRestrict {U V : S.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ structureModule U.toScheme) :
    M.restrict V.ι ≅ structureModule V.toScheme :=
  (moduleRestrictLEIso M h).symm ≪≫
    (restrictFunctor (S.homOfLE h)).mapIso e ≪≫ restrictUnitIso (S.homOfLE h)

/-- A line frame can be chosen affine and inside any prescribed base open. -/
theorem LocallyFreeRankOne.affine_frame (hM : LocallyFreeRankOne M)
    {V : S.Opens} {x : S} (hx : x ∈ V) :
    ∃ U : S.affineOpens, x ∈ U.1 ∧ U.1 ≤ V ∧
      Nonempty (M.restrict U.1.ι ≅ structureModule U.1.toScheme) := by
  obtain ⟨W, hxW, ⟨e⟩⟩ := hM x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ W ⊓ V from ⟨hxW, hx⟩) (W ⊓ V).isOpen
  exact ⟨⟨U, hU⟩, hxU, fun y hy ↦ (hUV hy).2,
    ⟨lineFrameRestrict (fun y hy ↦ (hUV hy).1) e⟩⟩

/-- Pulling a line back along a marking still gives affine local frames on the base. -/
theorem LocallyFreeRankOne.section_affine_frame {X : Scheme} {L : X.Modules}
    (hL : LocallyFreeRankOne L) (s : S ⟶ X) {V : S.Opens} {x : S} (hx : x ∈ V) :
    ∃ U : S.affineOpens, x ∈ U.1 ∧ U.1 ≤ V ∧
      Nonempty (((Scheme.Modules.pullback s).obj L).restrict U.1.ι ≅
        structureModule U.1.toScheme) :=
  (hL.pullback s).affine_frame hx

end FLT.Mazur.FCurve

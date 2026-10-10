/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DirectImageBaseChangeRestriction
public import FLT.Mazur.ProperLinePushforwardMate

/-!
# Proper line base change to arbitrary schemes

Residue acyclicity over the original Noetherian affine base makes the actual
base-change mate invertible over every changed base. The changed base need
not be affine or Noetherian: invertibility descends from its affine opens.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.LineSectionBaseChange
open FCurve DirectImageBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {P X T S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

include hL hV in
/-- The actual proper line mate is invertible over an unrestricted changed base. -/
theorem properLineBaseChangeMate_isIso_arbitrary :
    IsIso (comparison p q f g h.w.symm L) := by
  apply comparison_isIso_of_openCover p q f g h.w.symm L
    (fun U : T.affineOpens ↦ U.1)
  · intro x
    obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
      (U := ⊤) (x := x) (by trivial)
    exact ⟨⟨U, hU⟩, hx⟩
  · intro U
    exact properLineBaseChangeMate_isIso
      ((isPullback_morphismRestrict q U.1).flip.paste_horiz h) L hL hV

/-- Canonical proper direct-image base change, without a restriction on the new base. -/
@[irreducible] def properLineArbitraryBaseChangeIso :
    (pullback g).obj ((pushforward f).obj L) ≅
      (pushforward q).obj ((pullback p).obj L) := by
  letI := properLineBaseChangeMate_isIso_arbitrary h L hL hV
  exact asIso (comparison p q f g h.w.symm L)

/-- The unrestricted isomorphism retains the original independently defined mate. -/
lemma properLineArbitraryBaseChangeIso_hom :
    (properLineArbitraryBaseChangeIso h L hL hV).hom =
      comparison p q f g h.w.symm L := by
  unfold properLineArbitraryBaseChangeIso
  rfl

end FLT.Mazur.LineSectionBaseChange

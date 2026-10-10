/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineArbitraryBaseChange

/-!
# Iterated proper direct-image base change over unrestricted schemes

Residue vanishing on the original Noetherian affine base controls a further
base change even when neither changed base is Noetherian or affine.
The pasted-mate identity proves invertibility of the actual second mate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.LineSectionBaseChange
open FCurve DirectImageBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {Q P X U T S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))
  {r : Q ⟶ P} {t : Q ⟶ U} {k : U ⟶ T} (h' : IsPullback r t q k)

include h hL hV in
/-- The second actual mate is invertible without restrictions on either changed base. -/
theorem properLineIteratedMate_isIso :
    IsIso (comparison r t q k h'.w.symm ((pullback p).obj L)) := by
  let _ := properLineBaseChangeMate_isIso_arbitrary h L hL hV
  let _ := properLineBaseChangeMate_isIso_arbitrary (h'.paste_horiz h) L hL hV
  have hh := congrArg IsIso (comparison_paste p q f g h.w.symm r t k h'.w.symm L)
  have hi := (Iff.of_eq hh).mpr inferInstance
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using hi

/-- The canonical isomorphism for the actual second base-change mate. -/
@[irreducible] def properLineIteratedBaseChangeIso :
    (pullback k).obj ((pushforward q).obj ((pullback p).obj L)) ≅
      (pushforward t).obj ((pullback r).obj ((pullback p).obj L)) := by
  letI := properLineIteratedMate_isIso h L hL hV h'
  exact asIso (comparison r t q k h'.w.symm ((pullback p).obj L))

/-- Iterated base change retains the independently constructed second mate. -/
lemma properLineIteratedBaseChangeIso_hom :
    (properLineIteratedBaseChangeIso h L hL hV h').hom =
      comparison r t q k h'.w.symm ((pullback p).obj L) := by
  unfold properLineIteratedBaseChangeIso
  rfl

end FLT.Mazur.LineSectionBaseChange

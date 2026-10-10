/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankOneSectionDivisorUniqueness
public import FLT.Mazur.CartierAbelLocallySplit

/-!
# Uniqueness of relative Cartier divisors from rank-one direct image

For a surjective family, relative Cartier sections have locally split
direct-image maps. When that direct image is a line, equality of original
section orbits proves uniqueness of the full relative Abel fiber.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve

/-- A rank-one sheaf has actual finite free charts with a singleton basis. -/
theorem LocallyFreeRankOne.locallyFiniteFree {X : Scheme.{0}} {M : X.Modules}
    (hM : LocallyFreeRankOne M) : LocallyFiniteFree M := by
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := hM x
  refine ⟨U, hx, PUnit, inferInstance, ⟨e ≪≫ ?_⟩⟩
  exact (Limits.coproductUniqueIso (fun _ : PUnit ↦ structureModule U.toScheme)).symm

end FLT.Mazur.FCurve

namespace FLT.Mazur.CartierAbel
open FCurve
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
variable {X S : Scheme.{0}} (f : X ⟶ S) [Surjective f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hN : LocallyFreeRankOne ((pushforward f).obj L))

include hN in
/-- Any two relative Cartier sections give the same entire Abel-fiber element. -/
theorem rankOne_relativeSection_fiber_eq (s t : RelativeSection f L hL) :
    relativeSectionToFiber f L hL s = relativeSectionToFiber f L hL t := by
  apply Subtype.ext
  exact rankOne_twistedSection_fiber_eq f L hN s.val t.val
    (relativeSection_directImage_locallySplit f L hL hN.locallyFiniteFree s)
    (relativeSection_directImage_locallySplit f L hL hN.locallyFiniteFree t) hL

include hN in
/-- The equality of full zero ideals uses each original section, not just its support. -/
theorem rankOne_relativeSection_zeroIdeal_eq (s t : RelativeSection f L hL) :
    lineSectionZeroIdeal (twist_rankOne f L hL s.val.baseLine) s.val.section_ =
      lineSectionZeroIdeal (twist_rankOne f L hL t.val.baseLine) t.val.section_ :=
  congrArg (fun D : RelativeFiber f L hL ↦ D.val.val.val)
    (rankOne_relativeSection_fiber_eq f L hL hN s t)

include hN in
/-- A line direct image makes the actual relative Abel fiber a subsingleton. -/
theorem rankOne_relativeFiber_subsingleton : Subsingleton (RelativeFiber f L hL) := by
  refine ⟨fun D E ↦ ?_⟩
  obtain ⟨a, rfl⟩ := relativeQuotientToFiber_surjective f L hL D
  obtain ⟨b, rfl⟩ := relativeQuotientToFiber_surjective f L hL E
  induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
      exact rankOne_relativeSection_fiber_eq f L hL hN a b

end FLT.Mazur.CartierAbel

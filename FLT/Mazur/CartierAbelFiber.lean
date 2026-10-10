/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardTwistIso
public import FLT.Mazur.LineSectionDivisorCorrespondence

/-!
# Fibers of the Cartier divisor to relative Picard class map

The map uses the actual positive divisor sheaf. Its fibers retain full ideal
sheaves, and membership is characterized by actual base-line twists.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve
variable {X S : Scheme.{0}} (f : X ⟶ S)

/-- Effective Cartier divisors as full ideal sheaves. -/
abbrev Divisor (X : Scheme.{0}) := {I : X.IdealSheafData // EffectiveCartier I}

/-- The Abel class uses the actual sheaf of the effective Cartier divisor. -/
def abel (D : Divisor X) : SchemePicard.RelativePic f :=
  SchemePicard.relativeClass f (SchemePicard.mk (divisorLineBundle D.val D.property)
    D.property.divisorLineBundle_locallyFreeRankOne)

/-- The set-theoretic fiber over a specified line class, before representability. -/
def Fiber (L : X.Modules) (hL : LocallyFreeRankOne L) :=
  {D : Divisor X // abel f D = SchemePicard.relativeClass f (SchemePicard.mk L hL)}

/-- A Cartier divisor is in this Abel fiber exactly when its line is a base twist. -/
theorem mem_fiber_iff {L : X.Modules} (hL : LocallyFreeRankOne L) (D : Divisor X) :
    abel f D = SchemePicard.relativeClass f (SchemePicard.mk L hL) ↔
      ∃ B : SchemePicard.LineBundle S, Nonempty
        (divisorLineBundle D.val D.property ≅
          ModuleSheafTensor.tensor L ((pullback f).obj B.val)) := by
  exact eq_comm.trans (SchemePicard.relativeClass_mk_eq_iff_twist_iso f hL
    D.property.divisorLineBundle_locallyFreeRankOne)

/-- Recovering the zero divisor preserves the original relative line class. -/
theorem abel_zero {L : X.Modules} (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤))
    [Mono (globalSectionHom L s)] :
    abel f ⟨lineSectionZeroIdeal hL s, lineSectionZeroIdeal_effectiveCartier hL s⟩ =
      SchemePicard.relativeClass f (SchemePicard.mk L hL) := by
  apply congrArg (SchemePicard.relativeClass f)
  exact SchemePicard.mk_eq_of_iso _ hL (lineSectionZeroDivisorCanonicalIso hL s)

/-- Zero divisors of regular sections give points of the actual class fiber. -/
def zeroInFiber {L : X.Modules} (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤))
    [Mono (globalSectionHom L s)] : Fiber f L hL :=
  ⟨⟨lineSectionZeroIdeal hL s, lineSectionZeroIdeal_effectiveCartier hL s⟩,
    abel_zero f hL s⟩

end FLT.Mazur.CartierAbel

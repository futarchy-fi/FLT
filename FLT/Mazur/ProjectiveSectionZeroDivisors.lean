/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSectionDivisorCorrespondence

/-!
# Projective sections classified by their full Cartier zero ideals

On an integral scheme over a field with constant global functions, equality
of full zero ideals is equivalent to projective equality of nonzero sections.
This gives an injective map from projective sections to actual Cartier ideals.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (hc : HasConstantGlobalSections f)
    {L : X.Modules} (hL : LocallyFreeRankOne L)

include hc in
/-- Nonzero sections have the same full zero ideal exactly when they are projectively equal. -/
theorem lineSectionZeroIdeal_eq_iff_projective (s t : Γ(L, ⊤)) (hs : s ≠ 0) (ht : t ≠ 0) :
    let _ := Module.compHom Γ(L, ⊤) (structureScalarMap f)
    lineSectionZeroIdeal hL s = lineSectionZeroIdeal hL t ↔
      Projectivization.mk k s hs = Projectivization.mk k t ht := by
  let _ := Module.compHom Γ(L, ⊤) (structureScalarMap f)
  change _ ↔ Projectivization.mk k s hs = Projectivization.mk k t ht
  rw [eq_comm (a := lineSectionZeroIdeal hL s),
    nonzero_lineSectionZeroIdeal_eq_iff_iso hL hL t s ht hs]
  exact (projective_section_eq_iff_iso f hc hL s t hs ht).symm

/-- The actual Cartier zero ideal of a projective section class. -/
def projectiveSectionZeroDivisor :
    let _ := Module.compHom Γ(L, ⊤) (structureScalarMap f)
    Projectivization k Γ(L, ⊤) → {I : X.IdealSheafData // EffectiveCartier I} := by
  let _ := Module.compHom Γ(L, ⊤) (structureScalarMap f)
  change Projectivization k Γ(L, ⊤) → {I : X.IdealSheafData // EffectiveCartier I}
  intro p
  exact ⟨lineSectionZeroIdeal hL p.rep,
    nonzero_lineSectionZeroIdeal_effectiveCartier hL p.rep p.rep_nonzero⟩

include hc in
/-- The construction agrees with the full evaluation image of each nonzero representative. -/
lemma projectiveSectionZeroDivisor_mk (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    let _ := Module.compHom Γ(L, ⊤) (structureScalarMap f)
    (projectiveSectionZeroDivisor f hL (Projectivization.mk k s hs)).val =
      lineSectionZeroIdeal hL s := by
  let _ := Module.compHom Γ(L, ⊤) (structureScalarMap f)
  apply (lineSectionZeroIdeal_eq_iff_projective f hc hL _ _ _ hs).mpr
  exact Projectivization.mk_rep _

include hc in
/-- Full Cartier zero ideals distinguish projective section classes. -/
theorem projectiveSectionZeroDivisor_injective :
    let _ := Module.compHom Γ(L, ⊤) (structureScalarMap f)
    Function.Injective (projectiveSectionZeroDivisor f hL) := by
  let _ := Module.compHom Γ(L, ⊤) (structureScalarMap f)
  change Function.Injective (projectiveSectionZeroDivisor f hL)
  intro p q h
  have he := (lineSectionZeroIdeal_eq_iff_projective f hc hL p.rep q.rep
    p.rep_nonzero q.rep_nonzero).mp (congrArg Subtype.val h)
  simpa only [Projectivization.mk_rep] using he

end FLT.Mazur.FCurve

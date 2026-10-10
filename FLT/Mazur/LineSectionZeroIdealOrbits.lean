/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSectionZeroDivisor
public import FLT.Mazur.QuasicoherentImageIdealOrbits
public import FLT.Mazur.CurveLineSectionOrbits

/-!
# Zero ideals and actual section isomorphisms

Isomorphisms taking one section to another preserve its full zero ideal.
For regular sections equality of zero ideals is exactly a compatible
isomorphism of the dual evaluation embeddings. Projective equality over a
field with constant global functions therefore preserves the zero divisor.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

variable {X : Scheme.{0}} {L N : X.Modules}

/-- The dual evaluation commutes with transporting the original section. -/
lemma lineSectionEvaluation_naturality (a : L ⟶ N) (s : Γ(L, ⊤)) :
    moduleSheafDualMap L a ≫ lineSectionEvaluation s =
      lineSectionEvaluation (a.app ⊤ s) := by
  unfold lineSectionEvaluation
  rw [← Category.assoc, ← moduleSheafDualMap_comp, globalSectionHom_naturality]

/-- Isomorphic sections have equal full zero ideals, even for nonregular sections. -/
theorem lineSectionZeroIdeal_eq_of_iso (hL : LocallyFreeRankOne L)
    (hN : LocallyFreeRankOne N) (e : L ≅ N) (s : Γ(L, ⊤)) (t : Γ(N, ⊤))
    (he : e.hom.app ⊤ s = t) : lineSectionZeroIdeal hL s = lineSectionZeroIdeal hN t := by
  have := hL.dual.isFinitePresentation
  have := hN.dual.isFinitePresentation
  symm
  apply quasicoherentImageIdeal_eq_of_iso _ _ (moduleSheafDualIso L e)
  change moduleSheafDualMap L e.hom ≫ lineSectionEvaluation s = lineSectionEvaluation t
  rw [lineSectionEvaluation_naturality, he]

/-- Equality of zero ideals exactly classifies their regular dual evaluation embeddings. -/
theorem lineSectionZeroIdeal_eq_iff_dual_iso (hL : LocallyFreeRankOne L)
    (hN : LocallyFreeRankOne N) (s : Γ(L, ⊤)) (t : Γ(N, ⊤))
    [Mono (globalSectionHom L s)] [Mono (globalSectionHom N t)] :
    lineSectionZeroIdeal hL s = lineSectionZeroIdeal hN t ↔
      ∃ e : moduleSheafDual L ≅ moduleSheafDual N,
        e.hom ≫ lineSectionEvaluation t = lineSectionEvaluation s := by
  have := hL.dual.isFinitePresentation
  have := hN.dual.isFinitePresentation
  have := lineSectionEvaluation_mono hL s
  have := lineSectionEvaluation_mono hN t
  exact quasicoherentImageIdeal_eq_iff_iso _ _

/-- Projective equality preserves the full zero divisor, including its multiplicities. -/
theorem lineSectionZeroIdeal_eq_of_projective {k : Type} [Field k]
    (f : X ⟶ Spec (.of k)) (hc : HasConstantGlobalSections f)
    (hL : LocallyFreeRankOne L) (s t : Γ(L, ⊤)) (hs : s ≠ 0) (ht : t ≠ 0) :
    let _ := Module.compHom Γ(L, ⊤) (structureScalarMap f)
    Projectivization.mk k s hs = Projectivization.mk k t ht →
      lineSectionZeroIdeal hL s = lineSectionZeroIdeal hL t := by
  let _ := Module.compHom Γ(L, ⊤) (structureScalarMap f)
  change Projectivization.mk k s hs = Projectivization.mk k t ht → _
  intro h
  obtain ⟨e, he⟩ := (projective_section_eq_iff_iso f hc hL s t hs ht).mp h
  exact (lineSectionZeroIdeal_eq_of_iso hL hL e t s he).symm

end FLT.Mazur.FCurve

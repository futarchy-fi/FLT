/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteIdealConditionDimension
public import FLT.Mazur.NonzeroSectionPointCondition
public import FLT.Mazur.AmpleAcyclicNonzeroSection
public import FLT.Mazur.CurvePositiveDegreeSections

/-!
# Nonspecial lines with exactly one section on geometric curves

Starting with an acyclic line having a nonzero section, repeatedly impose a
Cartier rational-point condition. Each step preserves H¹ vanishing and reduces
H⁰ by one, so the process terminates at dimension one. Ample Serre vanishing
supplies the initial line on any nonempty proper smooth geometric curve.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve
open ModuleSheafTensor

variable {k : Type} [Field k] [IsAlgClosed k] {X : Scheme} [IsReduced X]
  (f : X ⟶ Spec (.of k)) [IsProper f] [SmoothOfRelativeDimension 1 f]

/-- Successive actual point conditions reduce any positive acyclic H⁰ to dimension one. -/
theorem exists_acyclic_rank_one_line_of_h0_pos {L : X.Modules}
    (hL : LocallyFreeRankOne L) [Subsingleton (ModuleScalarH f L 1)]
    (hp : 0 < Module.finrank k (ModuleScalarH f L 0)) :
    ∃ M : X.Modules, LocallyFreeRankOne M ∧ Subsingleton (ModuleScalarH f M 1) ∧
      Module.finrank k (ModuleScalarH f M 0) = 1 := by
  generalize hn : Module.finrank k (ModuleScalarH f L 0) = n at *
  induction n using Nat.strong_induction_on generalizing L with
  | h n ih =>
    by_cases h1 : n = 1
    · exact ⟨L, hL, inferInstance, hn.trans h1⟩
    obtain ⟨s, hs⟩ := exists_nonzero_section_of_h0_pos f L (hn.symm ▸ hp)
    obtain ⟨I, hI, hi, hsI⟩ := exists_cartier_point_condition f hL s hs
    let _ := hi
    obtain ⟨hz, hr⟩ := idealLine_acyclic_rank_drop_one f I hL s hsI
    let M := tensor (idealModule I) L
    have hM : LocallyFreeRankOne M := hI.idealModule_locallyFreeRankOne.tensor hL
    let _ : Subsingleton (ModuleScalarH f M 1) := hz
    change Module.finrank k (ModuleScalarH f M 0) + 1 =
      Module.finrank k (ModuleScalarH f L 0) at hr
    have hm : Module.finrank k (ModuleScalarH f M 0) < n := by omega
    have hmpos : 0 < Module.finrank k (ModuleScalarH f M 0) := by omega
    exact ih _ hm hM rfl hmpos

/-- Proper nonempty smooth curves over an algebraically closed field have nonspecial lines. -/
theorem exists_acyclic_rank_one_line_of_ample [Nonempty X]
    {B : X.Modules} (hB : AmpleLineBundle B) :
    ∃ M : X.Modules, LocallyFreeRankOne M ∧ Subsingleton (ModuleScalarH f M 1) ∧
      Module.finrank k (ModuleScalarH f M 0) = 1 := by
  obtain ⟨L, hL, hz, s, hs⟩ := exists_acyclic_line_nonzero_section f hB
  let _ := hz
  let _ := hL.isFinitePresentation
  let _ : Module.Finite k (ModuleScalarH f L 0) :=
    proper_coherent_hasFiniteCohomology f L 0
  let _ : Nontrivial (L.val.obj (Opposite.op ⊤)) := ⟨⟨s, 0, hs⟩⟩
  let _ : Nontrivial (ModuleScalarH f L 0) := (moduleScalarH0Equiv f L).toEquiv.nontrivial
  exact exists_acyclic_rank_one_line_of_h0_pos f hL Module.finrank_pos

end FLT.Mazur.FCurve

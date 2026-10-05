/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGeneratorScalar

/-!
# Generator opens of linear combinations

A linear combination can generate only where one of its summands generates.
This follows by taking section ratios on the combination's generator open,
where their scalar coordinates sum to one. No choice of line coordinates
or finite-generation assumption is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u v
namespace FLT.Mazur.FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (M : X.Modules)

/-- The zero section has empty generator open. -/
lemma sectionGeneratorOpen_zero : sectionGeneratorOpen M (0 : Γ(M, ⊤)) = ⊥ := by
  have h := sectionGeneratorOpen_smul M (0 : Γ(M, ⊤)) (0 : Γ(X, ⊤))
  simpa only [zero_smul, Scheme.basicOpen_zero, bot_inf_eq] using h

/-- The sum of two sections generates only where at least one summand does. -/
lemma sectionGeneratorOpen_add_le (s t : Γ(M, ⊤)) :
    sectionGeneratorOpen M (s + t) ≤ sectionGeneratorOpen M s ⊔ sectionGeneratorOpen M t := by
  let U := sectionGeneratorOpen M (s + t)
  let a := sectionRatioOn M (s + t) U le_rfl s
  let b := sectionRatioOn M (s + t) U le_rfl t
  have hab : a + b = (1 : Γ(X, U)) := by
    rw [← sectionRatioOn_self M (s + t) U le_rfl]
    simp only [a, b, sectionRatioOn, map_add]
  have hu := X.basicOpen_add_le a b
  rw [hab, X.basicOpen_one] at hu
  have ha := sectionRatioOn_basicOpen M (s + t) s U le_rfl
  have hb := sectionRatioOn_basicOpen M (s + t) t U le_rfl
  exact hu.trans (sup_le_sup (ha.le.trans inf_le_right) (hb.le.trans inf_le_right))

/-- Every section in a family's scalar span generates only in the union of its generator opens. -/
lemma sectionGeneratorOpen_le_of_mem_span {κ : Type v} (s : κ → Γ(M, ⊤))
    {t : Γ(M, ⊤)} (ht : t ∈ Submodule.span Γ(X, ⊤) (Set.range s)) :
    sectionGeneratorOpen M t ≤ ⨆ i, sectionGeneratorOpen M (s i) := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨i, rfl⟩ := ht
    exact le_iSup (fun i ↦ sectionGeneratorOpen M (s i)) i
  | zero => rw [sectionGeneratorOpen_zero]; exact bot_le
  | add a b _ _ ha hb => exact (sectionGeneratorOpen_add_le M a b).trans (sup_le ha hb)
  | smul r a _ ha => rw [sectionGeneratorOpen_smul]; exact inf_le_right.trans ha

end FLT.Mazur.FCurve

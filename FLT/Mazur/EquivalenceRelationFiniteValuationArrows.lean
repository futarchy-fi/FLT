/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationFiberRebase
public import FLT.Mazur.FinitePullbackValuationExtension

/-!
# Extending actual relation arrows using one full finite endpoint

Whole-fiber rebasing transports finiteness between the endpoints of any
original arrow. Over a valuation ring, a generic arrow and finiteness at
one full endpoint construct an arrow on the entire test and finiteness at
both endpoints. No finite component is substituted for either full source.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A T : Scheme.{0}} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- An actual original arrow identifies finiteness of its entire two endpoint pullbacks. -/
theorem finite_pullback_endpoints_iff (a : T ⟶ D) :
    IsFinite (pullback.snd p (a ≫ p)) ↔ IsFinite (pullback.snd p (a ≫ q)) := by
  let i := rebaseIso e a
  constructor
  · intro h
    let _ := h
    have hf : IsFinite (i.inv ≫ pullback.snd p (a ≫ p)) := inferInstance
    simpa only [i, rebaseIso, unrebase_snd] using hf
  · intro h
    let _ := h
    have hf : IsFinite (i.hom ≫ pullback.snd p (a ≫ q)) := inferInstance
    simpa only [i, rebaseIso, rebase_snd] using hf

include e in
/-- Specified endpoints retain this full-source equivalence on any coefficient scheme. -/
theorem finite_pullback_iff_of_arrow (x y : T ⟶ A) (a : T ⟶ D)
    (hx : a ≫ p = x) (hy : a ≫ q = y) :
    IsFinite (pullback.snd p x) ↔ IsFinite (pullback.snd p y) := by
  rw [← hx, ← hy]
  exact finite_pullback_endpoints_iff e a

variable {R K : Type} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] [A.IsSeparated]
local notation "η" => Spec.map (CommRingCat.ofHom (algebraMap R K))

include e

/-- One full finite endpoint extends a generic original arrow and makes both endpoints finite. -/
theorem valuation_arrow_of_finite_first (x y : Spec (.of R) ⟶ A)
    [IsFinite (pullback.snd p x)] (d : Spec (.of K) ⟶ D)
    (hx : d ≫ p = η ≫ x) (hy : d ≫ q = η ≫ y) :
    ∃ a : Spec (.of R) ⟶ D, η ≫ a = d ∧ a ≫ p = x ∧ a ≫ q = y ∧
      IsFinite (pullback.snd p y) := by
  obtain ⟨a, ha, hap, haq⟩ :=
    exists_valuation_two_endpoints_of_finite_pullback p q x y d hx hy
  exact ⟨a, ha, hap, haq, (finite_pullback_iff_of_arrow e x y a hap haq).mp inferInstance⟩

/-- Finiteness at either full endpoint suffices; symmetry supplies the other orientation. -/
theorem valuation_arrow_of_finite_endpoint (x y : Spec (.of R) ⟶ A)
    (hf : IsFinite (pullback.snd p x) ∨ IsFinite (pullback.snd p y))
    (d : Spec (.of K) ⟶ D) (hx : d ≫ p = η ≫ x) (hy : d ≫ q = η ≫ y) :
    ∃ a : Spec (.of R) ⟶ D, η ≫ a = d ∧ a ≫ p = x ∧ a ≫ q = y ∧
      IsFinite (pullback.snd p x) ∧ IsFinite (pullback.snd p y) := by
  rcases hf with hf | hf
  · let _ := hf
    obtain ⟨a, ha, hap, haq, hf'⟩ := valuation_arrow_of_finite_first e x y d hx hy
    exact ⟨a, ha, hap, haq, hf, hf'⟩
  · let _ := hf
    have hx' : (d ≫ e.s) ≫ p = η ≫ y := by rw [Category.assoc, e.symmetry₁, hy]
    have hy' : (d ≫ e.s) ≫ q = η ≫ x := by rw [Category.assoc, e.symmetry₂, hx]
    obtain ⟨a, _, hap, haq, hf'⟩ := valuation_arrow_of_finite_first e y x (d ≫ e.s) hx' hy'
    refine ⟨a ≫ e.s, ?_, ?_, ?_, hf', hf⟩
    · apply e.right_cancellation
      · simpa only [Category.assoc, e.symmetry₁, haq] using hx.symm
      · simpa only [Category.assoc, e.symmetry₂, hap] using hy.symm
    · rw [Category.assoc, e.symmetry₁, haq]
    · rw [Category.assoc, e.symmetry₂, hap]

/-- The extension is unique as an original arrow, keeping both endpoint equations. -/
theorem existsUnique_valuation_arrow_of_finite_first (x y : Spec (.of R) ⟶ A)
    [IsFinite (pullback.snd p x)] (d : Spec (.of K) ⟶ D)
    (hx : d ≫ p = η ≫ x) (hy : d ≫ q = η ≫ y) :
    ∃! a : Spec (.of R) ⟶ D, η ≫ a = d ∧ a ≫ p = x ∧ a ≫ q = y := by
  obtain ⟨a, ha, hap, haq, _⟩ := valuation_arrow_of_finite_first e x y d hx hy
  refine ⟨a, ⟨ha, hap, haq⟩, fun b hb ↦ ?_⟩
  apply e.right_cancellation
  · exact hb.2.1.trans hap.symm
  · exact hb.2.2.trans haq.symm

end FLT.Mazur.EquivalenceRelationFiber

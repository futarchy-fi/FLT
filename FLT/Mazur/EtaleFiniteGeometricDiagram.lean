/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Spreading finite geometric diagrams to a common étale scheme

Iterated actual scheme pullbacks extend a finite family of lifts on one test
simultaneously. The common scheme is étale over the original base, and the
whole test map, not merely its underlying point, is preserved.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EtaleFiniteGeometricDiagram
universe u
variable {Y T : Scheme.{u}}

/-- A finite diagram of lifts extends on one constructed étale neighborhood. -/
theorem exists_common {n : ℕ} (X : Fin n → Scheme.{u}) (f : ∀ i, X i ⟶ Y)
    [∀ i, Etale (f i)] (b : T ⟶ Y) (a : ∀ i, T ⟶ X i)
    (ha : ∀ i, a i ≫ f i = b) :
    ∃ (U : Scheme.{u}) (q : U ⟶ Y) (z : T ⟶ U) (r : ∀ i, U ⟶ X i),
      Etale q ∧ z ≫ q = b ∧ (∀ i, r i ≫ f i = q) ∧ (∀ i, z ≫ r i = a i) := by
  induction n with
  | zero =>
    exact ⟨Y, 𝟙 Y, b, fun i ↦ Fin.elim0 i, inferInstance, Category.comp_id _,
      fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨U, q, z, r, hq, hz, hr, he⟩ :=
      ih (fun i ↦ X i.succ) (fun i ↦ f i.succ) (fun i ↦ a i.succ)
        (fun i ↦ ha i.succ)
    let p : pullback q (f 0) ⟶ Y := pullback.fst q (f 0) ≫ q
    let w : T ⟶ pullback q (f 0) := pullback.lift z (a 0) (hz.trans (ha 0).symm)
    let s : ∀ i : Fin (n + 1), pullback q (f 0) ⟶ X i :=
      Fin.cases (pullback.snd q (f 0)) (fun i ↦ pullback.fst q (f 0) ≫ r i)
    refine ⟨pullback q (f 0), p, w, s, inferInstanceAs (Etale p), ?_, ?_, ?_⟩
    · change w ≫ pullback.fst q (f 0) ≫ q = b
      rw [← Category.assoc, pullback.lift_fst]
      exact hz
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact pullback.condition.symm
      · change (pullback.fst q (f 0) ≫ r j) ≫ f j.succ = p
        rw [Category.assoc, hr]
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact pullback.lift_snd _ _ _
      · change w ≫ pullback.fst q (f 0) ≫ r j = a j.succ
        rw [← Category.assoc, pullback.lift_fst]
        exact he j

end FLT.Mazur.EtaleFiniteGeometricDiagram

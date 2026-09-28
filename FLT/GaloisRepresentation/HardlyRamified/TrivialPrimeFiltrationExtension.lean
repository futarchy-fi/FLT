/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.TrivialPrimeFiltration
public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Extending filtrations of point groups

A trivial group killed by `p` gives a one-step filtration. An exact sequence
extends a filtration of its kernel when its quotient is trivial and killed by `p`.
-/

@[expose] public section

namespace ThreeAdicPlan.TrivialPrimeFiltration

variable {p : ℕ} {G A B C : Type*} [Group G]
  [AddCommGroup A] [DistribMulAction G A]
  [AddCommGroup B] [DistribMulAction G B]
  [AddCommGroup C] [DistribMulAction G C]

/-- A trivial action on a group killed by `p` has a one-step filtration. -/
def ofTrivial (hkill : ∀ a : A, p • a = 0) (htriv : ∀ (g : G) (a : A), g • a = a) :
    TrivialPrimeFiltration p G A where
  length := 1
  step i := if i = 0 then ⊥ else ⊤
  stepZero := by simp
  stepLength := by simp
  stepLe i hi := by
    have : i = 0 := by omega
    subst i
    simp
  nsmulMem i hi a _ := by
    have : i = 0 := by omega
    subst i
    simp [hkill]
  smulSubMem i hi g a _ := by
    have : i = 0 := by omega
    subst i
    simp [htriv]

/-- Extend a filtration along an exact sequence whose quotient is trivial and
killed by `p`. The maps retain the given action, without choosing any splitting. -/
def extension (F : TrivialPrimeFiltration p G A) (f : A →+[G] B) (g : B →+[G] C)
    (hex : ∀ b, g b = 0 ↔ ∃ a, f a = b)
    (hkill : ∀ c : C, p • c = 0) (htriv : ∀ (σ : G) (c : C), σ • c = c) :
    TrivialPrimeFiltration p G B where
  length := F.length + 1
  step i := if i ≤ F.length then (F.step i).map f.toAddMonoidHom else ⊤
  stepZero := by simp [F.stepZero]
  stepLength := by simp
  stepLe i hi := by
    by_cases h : i < F.length
    · simp only [ite_eq_left (by omega : i ≤ F.length), ite_eq_left (by omega : i + 1 ≤ F.length)]
      exact AddSubgroup.map_mono (F.stepLe i h)
    · have : i = F.length := by omega
      subst i
      simp
  nsmulMem i hi b hb := by
    by_cases h : i < F.length
    · simp only [ite_eq_left (by omega : i + 1 ≤ F.length)] at hb
      obtain ⟨a, ha, rfl⟩ := hb
      simp only [ite_eq_left (by omega : i ≤ F.length)]
      exact ⟨p • a, F.nsmulMem i h a ha, map_nsmul f p a⟩
    · have : i = F.length := by omega
      subst i
      simp only [le_refl, ite_true, F.stepLength]
      obtain ⟨a, ha⟩ := (hex (p • b)).mp (by rw [map_nsmul, hkill])
      exact ⟨a, AddSubgroup.mem_top a, ha⟩
  smulSubMem i hi σ b hb := by
    by_cases h : i < F.length
    · simp only [ite_eq_left (by omega : i + 1 ≤ F.length)] at hb
      obtain ⟨a, ha, rfl⟩ := hb
      simp only [ite_eq_left (by omega : i ≤ F.length)]
      refine ⟨σ • a - a, F.smulSubMem i h σ a ha, ?_⟩
      exact (map_sub f (σ • a) a).trans (by rw [map_smul]; rfl)
    · have : i = F.length := by omega
      subst i
      simp only [le_refl, ite_true, F.stepLength]
      obtain ⟨a, ha⟩ := (hex (σ • b - b)).mp (by rw [map_sub, map_smul, htriv, sub_self])
      exact ⟨a, AddSubgroup.mem_top a, ha⟩

end ThreeAdicPlan.TrivialPrimeFiltration

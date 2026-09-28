/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.TrivialPrimeFiltrationExtension

/-!
# Filtrations with a trivial kernel

Pullback along an injective equivariant map preserves a trivial-prime
filtration. An exact sequence with a trivial prime-torsion kernel prepends
a step to a filtration of its quotient. This is the order arising after duality.
-/

@[expose] public section

namespace ThreeAdicPlan.TrivialPrimeFiltration

variable {p : ℕ} {G A B C : Type*} [Group G]
  [AddCommGroup A] [DistribMulAction G A]
  [AddCommGroup B] [DistribMulAction G B]
  [AddCommGroup C] [DistribMulAction G C]

/-- Pull back a filtration through an injective equivariant additive map. -/
def comap (F : TrivialPrimeFiltration p G A) (f : B →+[G] A)
    (hf : Function.Injective f) : TrivialPrimeFiltration p G B where
  length := F.length
  step i := (F.step i).comap f.toAddMonoidHom
  stepZero := by
    ext b
    simp only [AddSubgroup.mem_comap, F.stepZero, AddSubgroup.mem_bot]
    exact ⟨fun h ↦ hf (h.trans (map_zero f).symm), fun h ↦ h ▸ map_zero f⟩
  stepLength := by simp [F.stepLength]
  stepLe i hi := AddSubgroup.comap_mono (F.stepLe i hi)
  nsmulMem i hi b hb := by
    change f (p • b) ∈ F.step i
    rw [map_nsmul]
    exact F.nsmulMem i hi (f b) hb
  smulSubMem i hi σ b hb := by
    change f (σ • b - b) ∈ F.step i
    rw [map_sub, map_smul]
    exact F.smulSubMem i hi σ (f b) hb

/-- Prepend a trivial prime-torsion kernel to a filtration of the quotient. -/
def coextension (F : TrivialPrimeFiltration p G C) (f : A →+[G] B) (g : B →+[G] C)
    (hex : ∀ b, g b = 0 ↔ ∃ a, f a = b)
    (hkill : ∀ a : A, p • a = 0) (htriv : ∀ (σ : G) (a : A), σ • a = a) :
    TrivialPrimeFiltration p G B where
  length := F.length + 1
  step i := if i = 0 then ⊥ else (F.step (i - 1)).comap g.toAddMonoidHom
  stepZero := by simp
  stepLength := by simp [F.stepLength]
  stepLe i hi := by
    by_cases h : i = 0
    · simp [h]
    · simp only [ite_eq_right h, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel]
      apply AddSubgroup.comap_mono
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ i)] using (F.stepLe (i - 1) (by omega))
  nsmulMem i hi b hb := by
    by_cases h : i = 0
    · subst i
      have hg : g b = 0 := by simpa [F.stepZero] using hb
      obtain ⟨a, rfl⟩ := (hex b).mp hg
      change p • f a = 0
      rw [← map_nsmul, hkill, map_zero]
    · simp only [ite_eq_right h, AddSubgroup.mem_comap]
      rw [map_nsmul]
      apply F.nsmulMem (i - 1) (by omega)
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ i)] using hb
  smulSubMem i hi σ b hb := by
    by_cases h : i = 0
    · subst i
      have hg : g b = 0 := by simpa [F.stepZero] using hb
      obtain ⟨a, rfl⟩ := (hex b).mp hg
      change σ • f a - f a = 0
      rw [← map_smul, htriv, sub_self]
    · simp only [ite_eq_right h, AddSubgroup.mem_comap]
      change g (σ • b - b) ∈ F.step (i - 1)
      rw [map_sub, map_smul]
      apply F.smulSubMem (i - 1) (by omega)
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ i)] using hb

end ThreeAdicPlan.TrivialPrimeFiltration

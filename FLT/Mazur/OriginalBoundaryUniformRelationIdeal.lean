/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryUniformRelationLift
public import FLT.Mazur.SchemeScalarAvoidanceIdeal
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# One ideal power for all original numerators on a solved relation open

Multipliers that solve every open-compatible raw numerator form an ideal
in the original invariants. Noetherianity of the arrow scheme puts the
avoidance ideal in its radical before any numerator is chosen. Finite
generation of a test ideal then gives one power for arbitrarily many
boundary coefficients; no infinite intersection of radicals is exchanged.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} (O : D.Opens)

/-- Original invariant scalars that solve every raw numerator already compatible on this open. -/
def originalRelationMultiplierIdeal : Ideal (compatibleFunctions p q) where
  carrier := {s | ∀ a : Γ(A, ⊤),
    O.ι.appTop (p.appTop a) = O.ι.appTop (q.appTop a) →
      s.val * a ∈ compatibleFunctions p q}
  zero_mem' := by
    intro a _
    change (0 : Γ(A, ⊤)) * a ∈ compatibleFunctions p q
    rw [zero_mul]
    exact zero_mem _
  add_mem' := by
    intro s r hs hr a ha
    change (s.val + r.val) * a ∈ compatibleFunctions p q
    rw [add_mul]
    exact add_mem (hs a ha) (hr a ha)
  smul_mem' := by
    intro s r hr a ha
    change (s.val * r.val) * a ∈ compatibleFunctions p q
    rw [mul_assoc]
    exact mul_mem s.property (hr a ha)

/-- Uniform relation multipliers give exact original lifts for any boundary of the numerator. -/
theorem originalRelationMultiplier_mem_liftIdeal
    (s : compatibleFunctions p q) (hs : s ∈ originalRelationMultiplierIdeal (p := p) O)
    (J : A.IdealSheafData) (a : Γ(A, ⊤))
    (ha : O.ι.appTop (p.appTop a) = O.ι.appTop (q.appTop a)) :
    s ∈ originalBoundaryLiftIdeal (p := p) (q := q) J (J.subschemeι.appTop a) := by
  exact ⟨⟨s.val * a, hs a ha⟩, map_mul _ _ _⟩

variable [IsNoetherian D]
local notation "σD" => p.appTop.hom.comp (Subring.subtype (compatibleFunctions p q))

/-- A uniform power is established before taking the ideal radical. -/
theorem relationAvoidanceIdeal_le_uniformMultiplier_radical :
    scalarAvoidanceIdeal σD O ≤
      (originalRelationMultiplierIdeal (p := p) (q := q) O).radical := by
  intro s hs
  obtain ⟨N, hN⟩ := exists_uniform_original_relation_multiplier O s
    ((mem_scalarAvoidanceIdeal_iff σD O s).mp hs)
  exact ⟨N, hN⟩

/-- Finite generation is required only of the specified original test ideal. -/
theorem exists_pow_le_originalRelationMultiplierIdeal
    (Q : Ideal (compatibleFunctions p q)) (hfg : Q.FG)
    (hQ : Q ≤ scalarAvoidanceIdeal σD O) :
    ∃ N : ℕ, Q ^ N ≤ originalRelationMultiplierIdeal (p := p) (q := q) O := by
  exact Ideal.exists_pow_le_of_le_radical_of_fg
    (hQ.trans (relationAvoidanceIdeal_le_uniformMultiplier_radical O)) hfg

/-- One ideal exponent lifts an arbitrary boundary family with raw representatives on one open. -/
theorem exists_pow_le_originalBoundaryLiftIdeals_of_common_relation_open
    (Q : Ideal (compatibleFunctions p q)) (hfg : Q.FG)
    (hQ : Q ≤ scalarAvoidanceIdeal σD O)
    (J : A.IdealSheafData) {ι : Type*} (t : ι → Γ(J.subscheme, ⊤))
    (hraw : ∀ i, ∃ a : Γ(A, ⊤), J.subschemeι.appTop a = t i ∧
      O.ι.appTop (p.appTop a) = O.ι.appTop (q.appTop a)) :
    ∃ N : ℕ, ∀ i, Q ^ N ≤ originalBoundaryLiftIdeal (p := p) (q := q) J (t i) := by
  obtain ⟨N, hN⟩ := exists_pow_le_originalRelationMultiplierIdeal O Q hfg hQ
  refine ⟨N, fun i s hs ↦ ?_⟩
  obtain ⟨a, ha, he⟩ := hraw i
  simpa only [ha] using originalRelationMultiplier_mem_liftIdeal O s (hN hs) J a he

end FLT.Mazur.EquivalenceRelationOrderedFrames

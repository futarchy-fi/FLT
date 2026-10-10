/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupAmple
public import FLT.Mazur.CompatibleSubgroupCyclic

/-!
# Ample cyclic levels on generalized elliptic curves

The level data retain the full generalized curve and its actual finite subgroup.
Both the fppf-local Cartier-generator condition and divisor ampleness are imposed.
Arbitrary base change and compatible isomorphisms preserve these conditions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

/-- Actual rank-n ample cyclic level data before taking isomorphism classes. -/
def ampleCyclicLevels (S : Scheme) (n : ℕ) :=
  {a : Σ E : GeneralizedEllipticCurve S, E.FiniteSubgroup n //
    a.2.IsCyclic ∧ a.2.IsAmple}

/-- Restrict both geometric objects and the proved level conditions. -/
def ampleCyclicLevelsPullback {S T : Scheme} (g : T ⟶ S) (n : ℕ)
    (a : ampleCyclicLevels S n) : ampleCyclicLevels T n :=
  ⟨⟨a.val.1.baseChange g, a.val.2.baseChange g⟩,
    a.property.1.baseChange a.val.2 g, a.property.2.baseChange g⟩

/-- The finite-subgroup equivalence relation restricted to genuine ample cyclic levels. -/
def ampleCyclicLevelSetoid (S : Scheme) (n : ℕ) : Setoid (ampleCyclicLevels S n) :=
  (compatibleIsoSetoid S n).comap Subtype.val

/-- Compatible isomorphisms transport both defining level conditions. -/
theorem CompatibleIso.ampleCyclic_iff {S : Scheme} {n : ℕ}
    {E F : GeneralizedEllipticCurve S} {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n}
    (a : CompatibleIso H J) : (H.IsCyclic ∧ H.IsAmple) ↔ (J.IsCyclic ∧ J.IsAmple) :=
  and_congr a.isCyclic_iff a.isAmple_iff

/-- Actual level pullback respects the restricted equivalence relation. -/
theorem ampleCyclicLevelsPullback_rel {S T : Scheme} (g : T ⟶ S) (n : ℕ)
    {a b : ampleCyclicLevels S n} (h : (ampleCyclicLevelSetoid S n).r a b) :
    (ampleCyclicLevelSetoid T n).r
      (ampleCyclicLevelsPullback g n a) (ampleCyclicLevelsPullback g n b) := by
  obtain ⟨e⟩ := h
  exact ⟨e.baseChange g⟩

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

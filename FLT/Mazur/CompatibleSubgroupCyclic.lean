/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupIsoBaseChange
public import FLT.Mazur.GeneralizedCurveCyclicSubgroup

/-!
# Cyclicity under compatible subgroup isomorphisms

Transport an actual generator on the same fppf cover using the pulled-back
compatible isomorphism. Thus cyclicity depends only on the geometric class.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

variable {S : Scheme} {n : ℕ} {E F : GeneralizedEllipticCurve S}
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n}

/-- Compatible isomorphisms transport cyclicity on the original fppf cover. -/
theorem CompatibleIso.isCyclic (a : CompatibleIso H J) (hH : H.IsCyclic) :
    J.IsCyclic := by
  obtain ⟨U, g, hf, hs, hl, P, hP⟩ := hH
  exact ⟨U, g, hf, hs, hl, P ≫ (a.baseChange g).subgroup.hom,
    (a.baseChange g).cartierGenerator hP⟩

/-- Cyclicity is invariant under compatible isomorphism. -/
theorem CompatibleIso.isCyclic_iff (a : CompatibleIso H J) : H.IsCyclic ↔ J.IsCyclic :=
  ⟨a.isCyclic, a.symm.isCyclic⟩

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

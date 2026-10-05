/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealTwistCohomologyStabilization
public import FLT.Mazur.LineSectionCohomologyAnnihilation

/-!
# Eventual vanishing of actual ideal-twist cohomology

Finite-stage annihilation now combines with the previously proved
stabilization. This proves eventual positive cohomology vanishing along a
nonzero line section with affine generator open on a proper integral curve.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve.LineSectionTwistSystem

variable {k : Type} [Field k] {X : Scheme} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

omit [IsIntegral X] in
/-- Each actual ideal-twist cohomology class is killed by a finite section transition. -/
theorem idealCohomology_annihilator (I : X.IdealSheafData)
    {L : X.Modules} (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤))
    (hs : IsAffineOpen (sectionGeneratorOpen L s)) (q n : ℕ)
    (x : (idealCohomology f s I (q + 1)).obj n) :
    ∃ (m : ℕ) (h : n ≤ m), (idealCohomology f s I (q + 1)).map (homOfLE h) x = 0 := by
  have := Chow.source_isNoetherian f
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have := FLT.Mazur.CoherentIdealIntersection.idealModule_coherent I
  exact exists_cohomology_annihilator (idealModule I) hL s hs f q n x

/-- The stable value of positive ideal-twist cohomology is zero. -/
theorem idealCohomology_eventually_subsingleton (hd : topologicalKrullDim X ≤ 1)
    (I : X.IdealSheafData) {L : X.Modules} (hL : LocallyFreeRankOne L)
    (s : Γ(L, ⊤)) (hs : s ≠ 0) (hAffine : IsAffineOpen (sectionGeneratorOpen L s))
    (q : ℕ) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → Subsingleton ((idealCohomology f s I (q + 1)).obj m) := by
  let F := idealCohomology f s I (q + 1)
  obtain ⟨n, hn⟩ := idealCohomology_eventually_isIso f hd I hL s hs (q + 1) (by omega)
  have hnzero : Subsingleton (F.obj n) := by
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨m, h, hm⟩ := idealCohomology_annihilator f I hL s hAffine q n x
    have : IsIso (F.map (homOfLE h)) := hn m h
    apply (ConcreteCategory.bijective_of_isIso (F.map (homOfLE h))).injective
    exact hm.trans (map_zero _).symm
  let := hnzero
  refine ⟨n, fun m h ↦ ?_⟩
  have : IsIso (F.map (homOfLE h)) := hn m h
  exact ((asIso (F.map (homOfLE h))).toLinearEquiv.symm).injective.subsingleton

end FLT.Mazur.FCurve.LineSectionTwistSystem

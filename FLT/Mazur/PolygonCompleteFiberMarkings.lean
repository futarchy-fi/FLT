/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteFamilyFlatness

/-!
# Retained markings on every base change of the actual complete polygon

The original disjoint complete sections induce disjoint sections on every
actual fiber. In particular all field-valued fibers, including geometric
generic fibers, are nonempty for the specified original markings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))

/-- The original complete marking, retained on the actual base change. -/
def completeFiberMarking (i : Fin n) : S ⟶ pullback (exactVeroneseProjToBase K n h) s :=
  pullback.lift (s ≫ completeBaseMarking K n h i) (𝟙 S)
    (by rw [Category.assoc, completeBaseMarking_toBase]; simp)

/-- The fiber marking retains the original labeled section in the total space. -/
@[reassoc (attr := simp)] theorem completeFiberMarking_fst (i : Fin n) :
    completeFiberMarking K n h s i ≫ pullback.fst _ _ = s ≫ completeBaseMarking K n h i :=
  pullback.lift_fst _ _ _

/-- The retained fiber marking is a section over its actual base. -/
@[reassoc (attr := simp)] theorem completeFiberMarking_snd (i : Fin n) :
    completeFiberMarking K n h s i ≫ pullback.snd _ _ = 𝟙 S :=
  pullback.lift_snd _ _ _

/-- The actual base-changed markings retain pairwise disjoint ranges. -/
theorem completeFiberMarkings_pairwise :
    Pairwise (fun i j ↦ Disjoint (Set.range (completeFiberMarking K n h s i))
      (Set.range (completeFiberMarking K n h s j))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨x, rfl⟩ ⟨y, he⟩
  have hp := congrArg (pullback.fst (exactVeroneseProjToBase K n h) s) he
  simp only [← Scheme.Hom.comp_apply, completeFiberMarking_fst] at hp
  exact Set.disjoint_left.mp (completeBaseMarkings_pairwise K n h hij)
    ⟨s x, rfl⟩ ⟨s y, hp⟩

/-- Every actual base change over a nonempty base is nonempty. -/
theorem completeFiber_nonempty [Nonempty S] :
    Nonempty ↥(pullback (exactVeroneseProjToBase K n h) s) :=
  Nonempty.map (completeFiberMarking K n h s ⟨0, by omega⟩) inferInstance

/-- Every retained marking remains a closed immersion on the actual base change. -/
theorem completeFiberMarking_isClosedImmersion (i : Fin n) :
    IsClosedImmersion (completeFiberMarking K n h s i) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsClosedImmersion (completeFiberMarking K n h s i ≫
      pullback.snd (exactVeroneseProjToBase K n h) s) := by
    rw [completeFiberMarking_snd]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.snd (exactVeroneseProjToBase K n h) s)

end FLT.Mazur.PolygonInfinitesimalStages

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticMarkingSpecialization

/-!
# Retained markings on every base change of the actual complete polygon

The original disjoint complete sections induce disjoint sections on every
actual fiber. In particular all field-valued fibers, including geometric
generic fibers, are nonempty for the specified original markings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S : Scheme} (s : S ⟶ Spec (.of A))

/-- The original complete marking, retained on the actual base change. -/
def completeFiberMarking (i : Fin n) : S ⟶ pullback (exactVeroneseProjToBase A π n h hne hgen) s :=
  pullback.lift (s ≫ completeBaseMarking A π hne hgen n h i) (𝟙 S)
    (by rw [Category.assoc, completeBaseMarking_toBase]; simp)

/-- The fiber marking retains the original labeled section in the total space. -/
@[reassoc (attr := simp)] theorem completeFiberMarking_fst (i : Fin n) :
    completeFiberMarking A π hne hgen n h s i ≫ pullback.fst _ _ = s ≫ completeBaseMarking A π hne
    hgen n h i :=
  pullback.lift_fst _ _ _

/-- The retained fiber marking is a section over its actual base. -/
@[reassoc (attr := simp)] theorem completeFiberMarking_snd (i : Fin n) :
    completeFiberMarking A π hne hgen n h s i ≫ pullback.snd _ _ = 𝟙 S :=
  pullback.lift_snd _ _ _

/-- The actual base-changed markings retain pairwise disjoint ranges. -/
theorem completeFiberMarkings_pairwise :
    Pairwise (fun i j ↦ Disjoint (Set.range (completeFiberMarking A π hne hgen n h s i))
      (Set.range (completeFiberMarking A π hne hgen n h s j))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨x, rfl⟩ ⟨y, he⟩
  have hp := congrArg (pullback.fst (exactVeroneseProjToBase A π n h hne hgen) s) he
  simp only [← Scheme.Hom.comp_apply, completeFiberMarking_fst] at hp
  exact Set.disjoint_left.mp (completeBaseMarkings_pairwise A π hgen hne n h hij)
    ⟨s x, rfl⟩ ⟨s y, hp⟩

/-- Every actual base change over a nonempty base is nonempty. -/
theorem completeFiber_nonempty [Nonempty S] :
    Nonempty ↥(pullback (exactVeroneseProjToBase A π n h hne hgen) s) :=
  Nonempty.map (completeFiberMarking A π hne hgen n h s ⟨0, by omega⟩) inferInstance

/-- Every retained marking remains a closed immersion on the actual base change. -/
theorem completeFiberMarking_isClosedImmersion (i : Fin n) :
    IsClosedImmersion (completeFiberMarking A π hne hgen n h s i) := by
  let _ := exactVeroneseProjToBase_isProper A π n h hne hgen
  let _ : IsClosedImmersion (completeFiberMarking A π hne hgen n h s i ≫
      pullback.snd (exactVeroneseProjToBase A π n h hne hgen) s) := by
    rw [completeFiberMarking_snd]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.snd (exactVeroneseProjToBase A π n h hne hgen) s)

/-- Original arithmetic markings are exactly the markings of the actual adic fibers. -/
@[reassoc] theorem originalStage_marking_fiber (m : ℕ) (i : Fin n) :
    marking A π m n h i ≫
      (originalStageToCompatibleProj_isPullback A π hne hgen n h m).isoPullback.hom =
        completeFiberMarking A π hne hgen n h (baseToIntegral A π m) i := by
  apply pullback.hom_ext
  · rw [Category.assoc, IsPullback.isoPullback_hom_fst, completeFiberMarking_fst,
      baseToIntegral_completeBaseMarking]
  · rw [Category.assoc, IsPullback.isoPullback_hom_snd, completeFiberMarking_snd, marking_base]

end FLT.Mazur.PolygonArithmeticStages

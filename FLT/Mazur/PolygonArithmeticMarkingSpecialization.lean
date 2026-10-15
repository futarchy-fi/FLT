/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCompleteMarkings
public import FLT.Mazur.PolygonArithmeticProperProj
public import FLT.Mazur.LocalBaseSectionDisjointness

/-!
# Closed specializations and disjointness of the complete markings

The closed point of the complete coefficient base is the actual image of the
original zeroth coefficient stage. The reconstructed markings retain the
distinct original closed points, so separatedness gives disjoint full sections.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] [IsLocalRing A] (π : A)
  (hgen : IsLocalRing.maximalIdeal A = ideal A π)

/-- The actual closed coefficient point maps to the closed point of the complete base. -/
theorem baseToIntegral_stageBasePoint (m : ℕ) :
    baseToIntegral A π m (stageBasePoint A π hgen m) = closedPoint A := by
  have he : residueBase A π (parameter_residue_zero A π hgen) m ≫
      baseToIntegral A π m = Spec.map (CommRingCat.ofHom (residue A)) := by
    rw [residueBase, baseToIntegral, ← Spec.map_comp]
    rfl
  change (residueBase A π (parameter_residue_zero A π hgen) m ≫
    baseToIntegral A π m) (default : Spec (.of (ResidueField A))) = _
  rw [he]
  exact IsLocalRing.PrimeSpectrum.comap_residue A _

variable [IsNoetherianRing A] [IsDomain A] (hne : π ≠ 0)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The complete marking specializes to the original closed-stage marked point. -/
theorem completeBaseMarking_closedPoint (i : Fin n) :
    completeBaseMarking A π hne hgen n h i (closedPoint A) =
      originalStageToCompatibleProj A π hne hgen n h 0 (marking A π 0 n h i (stageBasePoint A π
    hgen 0)) := by
  rw [← baseToIntegral_stageBasePoint A π hgen 0]
  exact congrArg (fun f : Spec (.of (Quotient A π 0)) ⟶ exactVeroneseProj A π n h hne hgen ↦
    f (stageBasePoint A π hgen 0)) (baseToIntegral_completeBaseMarking A π hne hgen n h i 0)

/-- Distinct original labels give distinct closed specializations of the complete markings. -/
theorem completeBaseMarking_closedPoint_ne {i j : Fin n} (hij : i ≠ j) :
    completeBaseMarking A π hne hgen n h i (closedPoint A) ≠
      completeBaseMarking A π hne hgen n h j (closedPoint A) := by
  rw [completeBaseMarking_closedPoint, completeBaseMarking_closedPoint]
  let _ := originalStageToCompatibleProj_isClosedImmersion A π hne hgen n h 0
  intro he
  have hm := (originalStageToCompatibleProj A π hne hgen n h 0).isClosedEmbedding.injective he
  exact Set.disjoint_left.mp (markings_pairwise A π 0 n h hij)
    ⟨stageBasePoint A π hgen 0, rfl⟩ ⟨stageBasePoint A π hgen 0, hm.symm⟩

/-- The actual complete-base sections have pairwise disjoint images. -/
theorem completeBaseMarkings_pairwise :
    Pairwise (fun i j ↦ Disjoint (Set.range (completeBaseMarking A π hne hgen n h i))
      (Set.range (completeBaseMarking A π hne hgen n h j))) := by
  let _ := exactVeroneseProjToBase_isProper A π n h hne hgen
  intro i j hij
  exact LocalBaseSectionDisjointness.disjoint_of_closedPoint_ne
    (exactVeroneseProjToBase A π n h hne hgen) _ _ (completeBaseMarking_toBase A π hne hgen n h i)
    (completeBaseMarking_toBase A π hne hgen n h j) (completeBaseMarking_closedPoint_ne A π hgen
    hne n h hij)

end FLT.Mazur.PolygonArithmeticStages

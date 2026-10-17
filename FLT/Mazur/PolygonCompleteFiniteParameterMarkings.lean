/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteFiniteParameterTranslation
public import FLT.Mazur.PolygonCompleteParameterOriginalLine
public import FLT.Mazur.PolygonCompleteDivisorRestriction
public import FLT.Mazur.PolygonInfinitesimalRotationDivisor

/-!
# Original labeled markings on the finite parameter product

The actual product comparison retains every original unit-one marking.
Translation moves it to the universal Laurent unit on the original rotated label.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "s" => Over.hom (completeFiniteParameterOver K m)
local notation "e" => completeFiniteParameterProductIso K n h m
local notation "q" => toBase (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h
local notation "u" => PolygonUniversalScaling.u (R := A)
local notation "z" => PolygonInfinitesimal.marking (A)[T;T⁻¹]
  (LaurentPolynomial.C (t)) n h

/-- The finite product comparison preserves each original labeled unit marking. -/
@[reassoc] theorem completeFiniteParameterProductIso_marking (i : Fin n) :
    (z) i 1 ≫ (e).hom = completeFiberMarking K n h (s) i := by
  have hf : (e).hom ≫ pullback.fst (exactVeroneseProjToBase K n h) (s) =
      scalingParameterProjection (A) (t) n h ≫ originalStageToCompatibleProj K n h m :=
    completeFiniteParameterProductIso_fst K n h m
  have hs : (e).hom ≫ pullback.snd (exactVeroneseProjToBase K n h) (s) = (q) :=
    completeFiniteParameterProductIso_snd K n h m
  apply pullback.hom_ext
  · erw [Category.assoc, hf,
      completeFiberMarking_fst]
    have hm := marking_parameterProjection LaurentPolynomial.C (t)
      (LaurentPolynomial.C (t)) rfl n h i (1 : (A)ˣ)
    simp only [map_one] at hm
    rw [← Category.assoc, scalingParameterProjection, hm, Category.assoc]
    change Spec.map (CommRingCat.ofHom LaurentPolynomial.C) ≫
      marking K m n h i ≫ originalStageToCompatibleProj K n h m = _
    rw [← baseToSeries_completeBaseMarking]
    rfl
  · erw [Category.assoc, hs,
      PolygonInfinitesimal.marking_base, completeFiberMarking_snd]

/-- The finite product comparison identifies the full original marking ideal. -/
theorem completeFiniteParameterProductIso_ideal :
    (∏ i : Fin n, (completeFiberMarking K n h (s) i).ker).comap (e).hom =
      markingDivisor (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h (fun _ ↦ 1) := by
  have hf : (e).hom ≫ pullback.fst (exactVeroneseProjToBase K n h) (s) =
      scalingParameterProjection (A) (t) n h ≫ originalStageToCompatibleProj K n h m :=
    completeFiniteParameterProductIso_fst K n h m
  rw [← completeMarkingDivisor_comap, ← Scheme.IdealSheafData.comap_comp, hf,
    Scheme.IdealSheafData.comap_comp,
    completeMarkingDivisor_originalBoundary, scalingParameterProjection,
    markingDivisor_parameterProjection]
  simp only [map_one]

/-- The existing universal scaling and rotation move each full marking to its actual label. -/
@[reassoc] theorem completeFiniteScalingRotation_marking (b : ZMod n) (i : Fin n) :
    (z) i 1 ≫ completeFiniteScalingRotation K n h m b =
      (z) (PolygonPinching.rotateIndex b i) (u) := by
  rw [completeFiniteScalingRotation, ← Category.assoc, marking_scaling,
    mul_one, marking_rotation]

/-- The original varying moved marking is exactly the old finite universal-unit marking. -/
@[reassoc] theorem completeFiniteParameterProductIso_movedMarking (b : ZMod n) (i : Fin n) :
    (z) (PolygonPinching.rotateIndex b i) (u) ≫ (e).hom =
      completeParameterMovedMarking K n h (completeFiniteParameter K n h m b) i := by
  rw [← completeFiniteScalingRotation_marking, Category.assoc,
    ← completeFiniteParameterTranslation, ← Category.assoc,
    completeFiniteParameterProductIso_marking]
  rfl

/-- The actual product identification is Cartesian over the unchanged Laurent base. -/
theorem completeFiniteParameterProductIso_isPullback :
    IsPullback (e).hom (q)
      (snd (completeOriginalWholeOver K n h) (completeFiniteParameterOver K m)).left
      (𝟙 _) := by
  apply IsPullback.of_horiz_isIso
  constructor
  rw [completeFiniteParameterProductIso_snd, Category.comp_id]

/-- The full moved ideal is exactly the old universal-unit divisor, with every multiplicity. -/
theorem completeFiniteParameterProductIso_movedIdeal (b : ZMod n) :
    (completeParameterMovedIdeal K n h (completeFiniteParameter K n h m b)).comap (e).hom =
      markingDivisor (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h (fun _ ↦ (u)) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsSeparated
      (snd (completeOriginalWholeOver K n h) (completeFiniteParameterOver K m)).left :=
    inferInstanceAs (IsSeparated (pullback.snd (exactVeroneseProjToBase K n h) (s)))
  rw [completeParameterMovedIdeal_eq_prod]
  have hp := section_prod_comap_of_cartesian
    (completeFiniteParameterProductIso_isPullback K n h m) Finset.univ
    (fun i ↦ (z) (PolygonPinching.rotateIndex b i) (u))
    (completeParameterMovedMarking K n h (completeFiniteParameter K n h m b))
    (fun i ↦ PolygonInfinitesimal.marking_base _ _ n h _ _)
    (completeParameterMovedMarking_snd K n h (completeFiniteParameter K n h m b))
    (fun i ↦ by
      rw [Category.id_comp]
      exact completeFiniteParameterProductIso_movedMarking K n h m b i)
  rw [hp]
  have hb : Function.Bijective (PolygonPinching.rotateIndex b : Fin n → Fin n) := by
    refine Function.bijective_iff_has_inverse.mpr
      ⟨PolygonPinching.rotateIndex (-b), ?_, ?_⟩
    · intro i
      rw [← PolygonPinching.rotateIndex_add, add_neg_cancel, PolygonPinching.rotateIndex_zero]
    · intro i
      rw [← PolygonPinching.rotateIndex_add, neg_add_cancel, PolygonPinching.rotateIndex_zero]
  exact Equiv.prod_comp (Equiv.ofBijective (PolygonPinching.rotateIndex b) hb)
    (fun i ↦ ((z) i (u)).ker)

end FLT.Mazur.PolygonInfinitesimalStages

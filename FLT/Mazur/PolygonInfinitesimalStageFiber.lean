/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalCoefficientTransport
public import FLT.Mazur.PolygonInfinitesimalSpecialFiber
public import FLT.Mazur.PolygonInfinitesimalStageReduction

/-!
# The original polygon is the actual closed fiber of each finite-order stage

The comparison is a pullback of the nonzero nilpotent family, composed with
the original split-node polygon identification. It preserves the arithmetic
base, all original node charts, and the unit-one markings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonInfinitesimal

set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K] (m n : ℕ) (h : 2 ≤ n)

/-- The actual zero-parameter fiber map into the finite-order family. -/
def zeroSpecialization : scheme K 0 n h ⟶ (family K m n h).left :=
  parameterProjection (reduction K m).toRingHom (parameter K m) 0
    (reduction_parameter K m) n h

/-- The zero-parameter assembled family is the actual pullback along reduction. -/
theorem zeroSpecialization_isPullback :
    IsPullback (zeroSpecialization K m n h) (toBase K 0 n h)
      (family K m n h).hom (reductionBase K m) :=
  parameterProjection_isPullback (reduction K m).toRingHom _ _ (reduction_parameter K m) n h

/-- The original cyclic polygon embeds into the actual finite-order family. -/
def specialFiberInclusion : PolygonCyclicAtlas.scheme K n h ⟶ (family K m n h).left :=
  (zeroFiberIso K n h).hom ≫ zeroSpecialization K m n h

/-- The original cyclic polygon identifies with the actual closed fiber. -/
def specialFiberPullbackIso : PolygonCyclicAtlas.scheme K n h ≅
    pullback (family K m n h).hom (reductionBase K m) :=
  zeroFiberIso K n h ≪≫ (zeroSpecialization_isPullback K m n h).isoPullback

/-- The closed-fiber comparison retains its inclusion into the nonzero nilpotent stage. -/
@[reassoc] theorem specialFiberPullbackIso_fst :
    (specialFiberPullbackIso K m n h).hom ≫ pullback.fst _ _ =
      specialFiberInclusion K m n h := by
  simp only [specialFiberPullbackIso, Iso.trans_hom, Category.assoc,
    IsPullback.isoPullback_hom_fst, specialFiberInclusion]

/-- The closed-fiber comparison retains the original polygon's structure map. -/
@[reassoc] theorem specialFiberPullbackIso_snd :
    (specialFiberPullbackIso K m n h).hom ≫ pullback.snd _ _ =
      PolygonCyclicAtlas.toBase K n h := by
  rw [specialFiberPullbackIso, Iso.trans_hom, Category.assoc,
    IsPullback.isoPullback_hom_snd, zeroFiberIso_base]

/-- The original cyclic polygon, with its original base, is the cartesian closed fiber. -/
theorem specialFiberInclusion_isPullback :
    IsPullback (specialFiberInclusion K m n h) (PolygonCyclicAtlas.toBase K n h)
      (family K m n h).hom (reductionBase K m) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (specialFiberPullbackIso K m n h)
    (specialFiberPullbackIso_fst K m n h) (specialFiberPullbackIso_snd K m n h)
  rw [← specialFiberPullbackIso_fst, ← specialFiberPullbackIso_snd,
    Category.assoc, Category.assoc, pullback.condition]

/-- Every original node chart retains its specified split-node comparison. -/
@[reassoc] theorem chart_specialFiberInclusion (i : Fin n) :
    PolygonCyclicAtlas.chart K n h i ≫ specialFiberInclusion K m n h =
      (PolygonSmoothing.specialFiberIso K).hom ≫ chart K 0 n h i ≫
        zeroSpecialization K m n h := by
  rw [specialFiberInclusion, chart_zeroFiberIso_assoc]

/-- The unit-one markings of the thickened family specialize to their actual zero sections. -/
@[reassoc] theorem marking_zeroSpecialization (i : Fin n) :
    PolygonInfinitesimal.marking K 0 n h i 1 ≫ zeroSpecialization K m n h =
      reductionBase K m ≫ marking K m n h i := by
  simpa only [map_one, marking, zeroSpecialization, reductionBase] using
    marking_parameterProjection (reduction K m).toRingHom
    (parameter K m) 0 (reduction_parameter K m) n h i 1

instance specialFiberInclusion_isClosedImmersion :
    IsClosedImmersion (specialFiberInclusion K m n h) :=
  MorphismProperty.of_isPullback (specialFiberInclusion_isPullback K m n h).flip inferInstance

instance specialFiberInclusion_surjective : Surjective (specialFiberInclusion K m n h) :=
  MorphismProperty.of_isPullback (specialFiberInclusion_isPullback K m n h).flip inferInstance

end FLT.Mazur.PolygonInfinitesimalStages

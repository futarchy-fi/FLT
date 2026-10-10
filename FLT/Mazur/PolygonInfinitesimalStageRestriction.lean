/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalCoefficientTransport
public import FLT.Mazur.PolygonInfinitesimalStages

/-!
# Adjacent concrete smoothing stages are actual pullbacks

The specified restriction R[q]/q^(m+2) → R[q]/q^(m+1) induces the assembled
family morphism. Its square is cartesian and it retains every unit-one marking.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonInfinitesimal

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (m n : ℕ) (h : 2 ≤ n)

/-- The specified closed-base restriction between adjacent coefficient spectra. -/
def baseRestriction : Spec (.of (Ring R m)) ⟶ Spec (.of (Ring R (m + 1))) :=
  Spec.map (CommRingCat.ofHom (restriction R m).toRingHom)

/-- The actual family restriction between successive infinitesimal stages. -/
def stageRestriction : (family R m n h).left ⟶ (family R (m + 1) n h).left :=
  parameterProjection (restriction R m).toRingHom (parameter R (m + 1)) (parameter R m)
    (restriction_parameter R m) n h

/-- Adjacent concrete stages form the actual coefficient pullback square. -/
theorem stageRestriction_isPullback :
    IsPullback (stageRestriction R m n h) (family R m n h).hom
      (family R (m + 1) n h).hom (baseRestriction R m) :=
  parameterProjection_isPullback (restriction R m).toRingHom _ _ (restriction_parameter R m) n h

/-- The actual restriction lies over the chosen truncated coefficient restriction. -/
@[reassoc] theorem stageRestriction_base :
    stageRestriction R m n h ≫ (family R (m + 1) n h).hom =
      (family R m n h).hom ≫ baseRestriction R m :=
  (stageRestriction_isPullback R m n h).w

/-- The lower-order family is the actual pullback of the next-order family. -/
def stageRestrictionIso : (family R m n h).left ≅
    pullback (family R (m + 1) n h).hom (baseRestriction R m) :=
  (stageRestriction_isPullback R m n h).isoPullback

@[reassoc] theorem stageRestrictionIso_fst :
    (stageRestrictionIso R m n h).hom ≫ pullback.fst _ _ = stageRestriction R m n h :=
  (stageRestriction_isPullback R m n h).isoPullback_hom_fst

@[reassoc] theorem stageRestrictionIso_snd :
    (stageRestrictionIso R m n h).hom ≫ pullback.snd _ _ = (family R m n h).hom :=
  (stageRestriction_isPullback R m n h).isoPullback_hom_snd

/-- Every distinguished unit-one marking survives the actual stage restriction. -/
@[reassoc] theorem marking_stageRestriction (i : Fin n) :
    marking R m n h i ≫ stageRestriction R m n h =
      baseRestriction R m ≫ marking R (m + 1) n h i := by
  simpa only [map_one, marking, stageRestriction, baseRestriction] using
    marking_parameterProjection (restriction R m).toRingHom
    (parameter R (m + 1)) (parameter R m) (restriction_parameter R m) n h i 1

/-- The adjacent-stage comparison retains the entire marked section. -/
theorem marking_stageRestrictionIso (i : Fin n) :
    marking R m n h i ≫ (stageRestrictionIso R m n h).hom =
      pullback.lift (baseRestriction R m ≫ marking R (m + 1) n h i) (𝟙 _)
        (by rw [Category.assoc, marking_base, Category.comp_id, Category.id_comp]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, stageRestrictionIso_fst, pullback.lift_fst, marking_stageRestriction]
  · rw [Category.assoc, stageRestrictionIso_snd, pullback.lift_snd, marking_base]

end FLT.Mazur.PolygonInfinitesimalStages

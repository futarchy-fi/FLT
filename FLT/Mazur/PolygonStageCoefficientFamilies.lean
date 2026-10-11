/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageCoefficientNaturality
public import FLT.Mazur.PolygonInfinitesimalStageRestriction
public import FLT.Mazur.PolygonPowerSeriesSystem

/-!
# Original marked stages under coefficient-ring change

The actual truncated coefficient map gives a cartesian family comparison.
It preserves all original unit-one markings and the map to the complete base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (m n : ℕ) (h : 2 ≤ n)

/-- The coefficient projection on the original finite base. -/
def stageCoefficientBase : Spec (.of (Ring S m)) ⟶ Spec (.of (Ring R m)) :=
  Spec.map (CommRingCat.ofHom (stageCoefficientMap f m))

/-- The original finite-family coefficient projection. -/
def stageCoefficientFamily : (family S m n h).left ⟶ (family R m n h).left :=
  PolygonInfinitesimal.parameterProjection (stageCoefficientMap f m)
    (parameter R m) (parameter S m) (stageCoefficientMap_parameter f m) n h

/-- The complete marked finite stage is the actual coefficient pullback. -/
theorem stageCoefficientFamily_isPullback :
    IsPullback (stageCoefficientFamily f m n h) (family S m n h).hom
      (family R m n h).hom (stageCoefficientBase f m) :=
  PolygonInfinitesimal.parameterProjection_isPullback (stageCoefficientMap f m)
    _ _ (stageCoefficientMap_parameter f m) n h

/-- Every original unit-one marking is retained by finite-stage coefficient change. -/
@[reassoc] theorem marking_stageCoefficientFamily (i : Fin n) :
    marking S m n h i ≫ stageCoefficientFamily f m n h =
      stageCoefficientBase f m ≫ marking R m n h i := by
  simpa only [map_one, marking, stageCoefficientFamily, stageCoefficientBase] using
    PolygonInfinitesimal.marking_parameterProjection (stageCoefficientMap f m)
      (parameter R m) (parameter S m) (stageCoefficientMap_parameter f m) n h i 1

/-- The original finite-base coefficient projection retains the complete coefficient map. -/
@[reassoc] theorem stageCoefficientBase_toSeries :
    stageCoefficientBase f m ≫ baseToSeries R m =
      baseToSeries S m ≫ Spec.map (CommRingCat.ofHom (PowerSeries.map f)) := by
  simp only [stageCoefficientBase, baseToSeries, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext s
  exact stageCoefficientMap_seriesToStage f m s

end FLT.Mazur.PolygonInfinitesimalStages

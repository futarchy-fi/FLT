/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonPowerSeriesBase
public import FLT.Mazur.PolygonInfinitesimalSystem

/-!
# The actual infinitesimal system over the complete coefficient spectrum

The compatible quotient maps make every truncated base and polygon a scheme
over the same power-series spectrum. The specified markings are sections of
this system over that spectrum.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace FLT.Mazur.PolygonInfinitesimalStages

variable (R : Type u) [CommRing R]

/-- Each actual truncated base is a closed subscheme of the complete base spectrum. -/
def baseToSeries (m : ℕ) :
    Spec (.of (Ring R m)) ⟶ Spec (.of (PowerSeries R)) :=
  Spec.map (CommRingCat.ofHom (seriesToStage R m).toRingHom)

instance baseToSeries_isClosedImmersion (m : ℕ) : IsClosedImmersion (baseToSeries R m) :=
  IsClosedImmersion.spec_of_surjective _ (seriesToStage_surjective R m)

/-- The adjacent actual base inclusions commute over the power-series spectrum. -/
@[reassoc] theorem baseRestriction_toSeries (m : ℕ) :
    baseRestriction R m ≫ baseToSeries R (m + 1) = baseToSeries R m := by
  rw [baseRestriction, baseToSeries, ← Spec.map_comp]
  exact congrArg (fun f : PowerSeries R →ₐ[R] Ring R m ↦
    Spec.map (CommRingCat.ofHom f.toRingHom)) (restriction_seriesToStage R m)

/-- All coefficient transitions are compatible over the complete spectrum. -/
def baseSeriesStructure :
    baseSystem R ⟶ (Functor.const ℕ).obj (Spec (.of (PowerSeries R))) :=
  NatTrans.ofSequence (baseToSeries R) (by
    intro m
    change (Functor.ofSequence (baseRestriction R)).map (homOfLE (Nat.le_succ m)) ≫
      baseToSeries R (m + 1) = baseToSeries R m ≫ 𝟙 _
    rw [Functor.ofSequence_map_homOfLE_succ, Category.comp_id]
    exact baseRestriction_toSeries R m)

/-- The complete spectrum is an actual cocone on the system of infinitesimal bases. -/
def baseSeriesCocone : Cocone (baseSystem R) :=
  ⟨Spec (.of (PowerSeries R)), baseSeriesStructure R⟩

variable (n : ℕ) (h : 2 ≤ n)

/-- The assembled polygon system lies over the actual complete coefficient spectrum. -/
def stageSeriesStructure :
    stageSystem R n h ⟶ (Functor.const ℕ).obj (Spec (.of (PowerSeries R))) :=
  systemStructure R n h ≫ baseSeriesStructure R

/-- Every original unit-one marking retains its structure map to the complete base. -/
theorem systemMarking_series (i : Fin n) :
    systemMarking R n h i ≫ stageSeriesStructure R n h = baseSeriesStructure R := by
  rw [stageSeriesStructure, ← Category.assoc, systemMarking_structure, Category.id_comp]

/-- Every transition of the actual polygon system commutes over the complete base. -/
@[reassoc] theorem stageSystem_toSeries {a b : ℕ} (f : a ⟶ b) :
    (stageSystem R n h).map f ≫ (family R b n h).hom ≫ baseToSeries R b =
      (family R a n h).hom ≫ baseToSeries R a := by
  have hn := (stageSeriesStructure R n h).naturality f
  change (stageSystem R n h).map f ≫ (family R b n h).hom ≫ baseToSeries R b =
    ((family R a n h).hom ≫ baseToSeries R a) ≫ 𝟙 _ at hn
  simpa only [Category.comp_id] using hn

end FLT.Mazur.PolygonInfinitesimalStages

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXIncidenceNodeRestriction
public import FLT.Mazur.WeierstrassModificationXIncidenceLaurentBoundary
public import FLT.Mazur.WeierstrassModificationXLaurentNodeRestriction

/-!
# Exact incidence squares for both full initial neighborhoods

The original boundary has the desired inverse parameter after the incidence
morphism, and the opposite full neighborhood gives the same morphism. These
are morphism equalities, with no assertion that the incidence map is an embedding.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The polygon incidence map retains the full reflection invariance. -/
theorem incidencePolygonMap_reflection :
    ((initialReflection W s b3 b4 b6).restrictScalars R).toAlgHom.comp
      (incidencePolygonMap W s b3 b4 b6) = incidencePolygonMap W s b3 b4 b6 := by
  rw [incidencePolygonMap, ← AlgHom.comp_assoc, incidenceNodeMap_reflection]

/-- Reflection fixes the original incidence morphism on the entire original chart. -/
@[reassoc] theorem incidencePolygonMorphism_reflection :
    Spec.map (CommRingCat.ofHom (initialReflection W s b3 b4 b6).toRingHom) ≫
      incidencePolygonMorphism W s b3 b4 b6 = incidencePolygonMorphism W s b3 b4 b6 := by
  rw [incidencePolygonMorphism, ← Spec.map_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f.toRingHom))
    (incidencePolygonMap_reflection W s b3 b4 b6)

variable (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)

/-- The opposite full neighborhood has the same complete incidence restriction. -/
@[reassoc] theorem polynomialOppositeNodeChart_incidence :
    polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hrI h3 ≫
      incidencePolygonMorphism W s b3 b4 b6 =
        incidenceInitialMorphism W s b3 b4 b6 r hr I hI hrI h3 := by
  have hf : polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hrI h3 =
      polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3 ≫
        Spec.map (CommRingCat.ofHom (initialReflection W s b3 b4 b6).toRingHom) := by
    rw [polynomialOppositeNodeChart_eq_spec, polynomialNodeChart_eq_spec, ← Spec.map_comp]
    rfl
  rw [hf, Category.assoc, incidencePolygonMorphism_reflection, polynomialNodeChart_incidence]

variable (ha : IsUnit W.a₁) (hs : s ∈ I) (h2 : W.a₂ ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "r₀" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hr₀" => polynomialSlopeRoot_equation W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hm₀" => polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "G" => laurentNodeRestriction W s b3 b4 b6 I hI ha hs h2 h3 h4 h6

/-- The original full Laurent boundary commutes exactly after the incidence restriction. -/
@[reassoc] theorem incidenceInitialMorphism_boundary :
    Spec.map (CommRingCat.ofHom (G).toRingHom) ≫
      incidenceInitialMorphism W s b3 b4 b6 r₀ hr₀ I hI hm₀ h3 =
        (PolygonSmoothing.edgeInversion R).hom ≫ PolygonSmoothing.leftBranchOpen R s := by
  rw [← polynomialNodeChart_incidence, ← Category.assoc, laurentNodeRestriction_first_spec]
  exact incidencePolygonMorphism_laurent ..

end FLT.Mazur.WeierstrassModificationX

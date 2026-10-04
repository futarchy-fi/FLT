/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicComponentSection
public import FLT.Mazur.PolygonCubicGenerationCover
public import FLT.Mazur.ModuleSectionIsomorphismTransport

/-!
# The uniform interior section generates on polygon torus opens

Invertibility on the Laurent chart transports through the actual component
comparison and composed pullbacks to the polygon's open torus immersion.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open FCurve PolygonPinching PolygonPowerNodeEndpoints ProjectiveLineMarkedHZero
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- The actual pulled-back interior section is a generator on each polygon torus chart. -/
theorem interiorSection_isIso_torus (i : Fin n) :
    IsIso (globalSectionHom _
      (pullGlobal (torusToComponent K ≫ componentι K n i ≫ p).left
        (polygonLine K n hn p q h a 3) (nodeSection K n hn p q h a 0 1 0))) := by
  let s := nodeSection K n hn p q h a 0 1 0
  let t := componentSection K n hn p q h a s i
  have ht := interiorSection_isIso K (a i) 3 t
    (interior_component_polynomial K n hn p q h a i)
  have hc := globalSectionHom_isIso_comp_pullGlobal
    (ProjectiveLine.overlapLeft K) (ProjectiveLine.left K) _ t
  change IsIso (globalSectionHom _ (pullGlobal (torusToComponent K).left
    (ProjectiveLineMarkedSectionTransition.line K (a i) 3) t)) at hc
  dsimp only [t, componentSection] at hc
  have hb := globalSectionHom_isIso_pullback_transport (torusToComponent K).left
    (PolygonDirectPowerComparison.lineIso K n hn p q h a i 3)
    (pullGlobal (componentι K n i ≫ p).left _ s)
  exact globalSectionHom_isIso_comp_pullGlobal (torusToComponent K).left
    (componentι K n i ≫ p).left _ s

/-- The same actual section trivializes its sheaf on the open image in the polygon. -/
theorem interiorSection_isIso_torusOpen (i : Fin n) :
    IsIso (sectionHom (polygonLine K n hn p q h a 3) (torusOpen K n hn p q h i)
      ((polygonLine K n hn p q h a 3).presheaf.map (homOfLE le_top).op
        (nodeSection K n hn p q h a 0 1 0))) := by
  have := interiorSection_isIso_torus K n hn p q h a i
  let := torus_isOpenImmersion K n hn p q h i
  exact sectionHom_isIso_on_image (torusToComponent K ≫ componentι K n i ≫ p).left _ _

end FLT.Mazur.PolygonCubicSections

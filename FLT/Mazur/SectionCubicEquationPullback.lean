/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SectionCubicMorphism
public import FLT.Mazur.ModuleSectionProjectiveNaturality

/-!
# Original normalized cubic equations under scheme pullback

The actual coefficient and section maps transport the equations to every
inverse-image generator chart. The constructed cubic morphism commutes with
this pullback, including nonreduced arithmetic stages.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme} (f : X ⟶ Y) (M : Y.Modules)
  {R : Type} [CommRing R] (W : WeierstrassCurve R) (t : Fin 3 → Γ(M, ⊤))

/-- The three normalized polynomial identities, expressed independently of the source model. -/
def CubicCoordinateEquations (r : R →+* Γ(Y, ⊤)) : Prop :=
  ∀ j, (W.map (sectionChartScalars r (sectionGeneratorOpen M (t j)))).toProjective.Equation
    (fun i ↦ sectionRatioOn M (t j) (sectionGeneratorOpen M (t j)) le_rfl (t i))

/-- A source-independent wrapper prevents expansion of concrete arithmetic family models. -/
def coordinateCubicMorphism (ht : (⨆ i, sectionGeneratorOpen M (t i)) = ⊤)
    (r : R →+* Γ(Y, ⊤)) (he : CubicCoordinateEquations M W t r) : Y ⟶ integralCurve W :=
  sectionCubicMorphism M W t ht r he

/-- The wrapped coordinate construction retains the original projective morphism. -/
@[reassoc] theorem coordinateCubicMorphism_projective
    (ht : (⨆ i, sectionGeneratorOpen M (t i)) = ⊤)
    (r : R →+* Γ(Y, ⊤)) (he : CubicCoordinateEquations M W t r) :
    coordinateCubicMorphism M W t ht r he ≫ integralProjectiveMap W =
      sectionProjectiveMorphism M 2 t ht r :=
  sectionCubicMorphism_projective M W t ht r he

/-- The original normalized equation transports to any permitted source subopen. -/
theorem sectionCubicEquation_pullback (j : Fin 3) (U : Y.Opens) (V : X.Opens)
    (hV : V ≤ f ⁻¹ᵁ U) (hi : U ≤ sectionGeneratorOpen M (t j))
    (hiV : V ≤ sectionGeneratorOpen ((pullback f).obj M) (pullGlobal f M (t j)))
    (r : R →+* Γ(Y, U))
    (he : (W.map r).toProjective.Equation (fun i ↦ sectionRatioOn M (t j) U hi (t i))) :
    (W.map ((f.appLE U V hV).hom.comp r)).toProjective.Equation
      (fun i ↦ sectionRatioOn ((pullback f).obj M) (pullGlobal f M (t j)) V hiV
        (pullGlobal f M (t i))) := by
  have h := he.map (f.appLE U V hV).hom
  change ((W.map r).map (f.appLE U V hV).hom).toProjective.Equation
    (fun i ↦ f.appLE U V hV (sectionRatioOn M (t j) U hi (t i))) at h
  simpa only [WeierstrassCurve.map_map,
    sectionRatioOn_pullback f M U V hV _ _ hi hiV] using h

variable (hM : LocallyFreeRankOne M) (ht : (⨆ i, sectionGeneratorOpen M (t i)) = ⊤)
  (r : R →+* Γ(Y, ⊤))
  (he : ∀ j, (W.map (sectionChartScalars r (sectionGeneratorOpen M (t j)))).toProjective.Equation
    (fun i ↦ sectionRatioOn M (t j) (sectionGeneratorOpen M (t j)) le_rfl (t i)))

include hM he in
/-- All original generator-chart equations hold for the actual pulled-back coordinates. -/
theorem sectionCubicEquations_pullback (j : Fin 3) :
    (W.map (sectionChartScalars (f.appTop.hom.comp r)
      (sectionGeneratorOpen ((pullback f).obj M) (pullGlobal f M (t j))))).toProjective.Equation
        (fun i ↦ sectionRatioOn ((pullback f).obj M) (pullGlobal f M (t j))
          (sectionGeneratorOpen ((pullback f).obj M) (pullGlobal f M (t j))) le_rfl
            (pullGlobal f M (t i))) := by
  have hV := (sectionGeneratorOpen_pullGlobal hM f (t j)).le
  have h := sectionCubicEquation_pullback f M W t j _ _ hV le_rfl le_rfl _ (he j)
  rwa [sectionChartScalars_pullback] at h

/-- The actual equation-constructed cubic morphism commutes with arbitrary base restriction. -/
theorem sectionCubicMorphism_pullback :
    f ≫ sectionCubicMorphism M W t ht r he =
      sectionCubicMorphism ((pullback f).obj M) W (fun i ↦ pullGlobal f M (t i))
        (sectionGeneratorCover_pullback f M hM 2 t ht) (f.appTop.hom.comp r)
          (sectionCubicEquations_pullback f M W t hM r he) := by
  apply (cancel_mono (integralProjectiveMap W)).mp
  rw [Category.assoc, sectionCubicMorphism_projective, sectionCubicMorphism_projective,
    sectionProjectiveMorphism_pullback f M hM]

end FLT.Mazur.FCurve

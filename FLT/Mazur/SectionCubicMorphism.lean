/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SectionCubicChartMorphism
public import FLT.Mazur.ModuleSectionProjectiveOver

/-!
# Constructing a cubic morphism from normalized equations

Three generating sections satisfying the specified Weierstrass equation on
their generator opens give a unique morphism to that cubic. No cubic-valued
map or overlap compatibility is supplied as input.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme} (M : X.Modules) {R : Type} [CommRing R]
  (W : WeierstrassCurve R) (t : Fin 3 → Γ(M, ⊤))
  (ht : (⨆ i, sectionGeneratorOpen M (t i)) = ⊤) (r : R →+* Γ(X, ⊤))
  (he : ∀ j, (W.map (sectionChartScalars r (sectionGeneratorOpen M (t j)))).toProjective.Equation
    (fun i ↦ sectionRatioOn M (t j) (sectionGeneratorOpen M (t j)) le_rfl (t i)))

/-- The concrete cubic morphism on each original generator open. -/
def sectionCubicLocal (j : Fin 3) :
    (sectionGeneratorOpen M (t j)).toScheme ⟶ integralCurve W :=
  sectionCubicChartMorphism M W t j _ le_rfl (sectionChartScalars r _) (he j)

/-- Each local cubic map has the prescribed projective coordinates. -/
@[reassoc] theorem sectionCubicLocal_projective (j : Fin 3) :
    sectionCubicLocal M W t r he j ≫ integralProjectiveMap W =
      (sectionGeneratorOpen M (t j)).ι ≫ sectionProjectiveMorphism M 2 t ht r := by
  rw [sectionCubicLocal, sectionCubicChartMorphism_projectiveMap,
    sectionGeneratorOpen_ι_projectiveMorphism]
  rfl

include ht in
/-- Actual overlap compatibility follows from the common projective coordinates. -/
theorem sectionCubicLocal_compatible (j k : Fin 3) :
    pullback.fst (sectionGeneratorOpen M (t j)).ι (sectionGeneratorOpen M (t k)).ι ≫
        sectionCubicLocal M W t r he j =
      pullback.snd (sectionGeneratorOpen M (t j)).ι (sectionGeneratorOpen M (t k)).ι ≫
        sectionCubicLocal M W t r he k := by
  apply (cancel_mono (integralProjectiveMap W)).mp
  simp only [Category.assoc, sectionCubicLocal_projective M W t ht r he]
  rw [← Category.assoc, ← Category.assoc, pullback.condition]

/-- The cubic-valued morphism constructed from the original normalized coordinate equations. -/
def sectionCubicMorphism : X ⟶ integralCurve W :=
  (sectionGeneratorCover M 2 t ht).glueMorphisms (sectionCubicLocal M W t r he)
    (sectionCubicLocal_compatible M W t ht r he)

/-- Gluing retains each concrete chart morphism. -/
@[reassoc] theorem sectionCubicMorphism_onChart (j : Fin 3) :
    (sectionGeneratorOpen M (t j)).ι ≫ sectionCubicMorphism M W t ht r he =
      sectionCubicLocal M W t r he j :=
  (sectionGeneratorCover M 2 t ht).ι_glueMorphisms _ _ j

/-- The constructed cubic morphism retains the entire original projective map. -/
@[reassoc] theorem sectionCubicMorphism_projective :
    sectionCubicMorphism M W t ht r he ≫ integralProjectiveMap W =
      sectionProjectiveMorphism M 2 t ht r := by
  apply (sectionGeneratorCover M 2 t ht).hom_ext
  intro j
  change (sectionGeneratorOpen M (t j)).ι ≫ _ =
    (sectionGeneratorOpen M (t j)).ι ≫ _
  rw [sectionCubicMorphism_onChart_assoc M W t ht r he j, sectionCubicLocal_projective]

/-- The given coordinate presentation determines the cubic morphism uniquely. -/
theorem sectionCubicMorphism_unique (g : X ⟶ integralCurve W)
    (hg : g ≫ integralProjectiveMap W = sectionProjectiveMorphism M 2 t ht r) :
    g = sectionCubicMorphism M W t ht r he := by
  apply (cancel_mono (integralProjectiveMap W)).mp
  rw [hg, sectionCubicMorphism_projective]

end FLT.Mazur.FCurve

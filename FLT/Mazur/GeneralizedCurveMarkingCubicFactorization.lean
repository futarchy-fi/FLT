/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingChartEquation
public import FLT.Mazur.SectionCubicChartMorphism

/-!
# The original family maps to its integral Weierstrass cubic

The normalized chart equations give cubic-valued morphisms on the actual
generator cover. The closed projective embedding detects their agreement,
so they glue to a global factorization over the original base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  Scheme.Modules.pullback ModuleSheafTensor.tensor

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

local instance generalizedCurveMarkingCubicFactorizationProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (Scheme.Modules.pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "L" => divisorLineBundle (Scheme.Hom.ker (Over.Hom.left (t))) (hI)
local notation "T" => smoothMarkingProjectiveSections E s e
local notation "W" => smoothMarkingWeierstrassCurve E s e
local notation "C" => sectionGeneratorCover (tensorPower (L) 3) 2 (T)
  (smoothMarkingProjectiveSections_cover E s e)

/-- The cubic-valued morphism on each original generator open. -/
def smoothMarkingCubicLocal (j : Fin 3) : (C).X j ⟶ integralCurve (W) :=
  sectionCubicChartMorphism (tensorPower (L) 3) (W) (T) j _ le_rfl
    (sectionChartScalars E.curve.hom.appTop.hom _)
    (smoothMarkingChartCoordinates_equation E s e j _ le_rfl)

/-- Each local cubic morphism retains the original projective map. -/
@[reassoc] theorem smoothMarkingCubicLocal_projective (j : Fin 3) :
    smoothMarkingCubicLocal E s e j ≫ integralProjectiveMap (W) =
      (C).f j ≫ smoothMarkingToProjectiveSpace E s e := by
  rw [smoothMarkingCubicLocal, sectionCubicChartMorphism_projectiveMap]
  exact (sectionGeneratorOpen_ι_projectiveMorphism (tensorPower (L) 3) 2 (T)
    (smoothMarkingProjectiveSections_cover E s e) E.curve.hom.appTop.hom j).symm

/-- The local cubic morphisms agree on the actual categorical overlaps. -/
theorem smoothMarkingCubicLocal_compatible (i j : Fin 3) :
    pullback.fst ((C).f i) ((C).f j) ≫ smoothMarkingCubicLocal E s e i =
      pullback.snd ((C).f i) ((C).f j) ≫ smoothMarkingCubicLocal E s e j := by
  apply (cancel_mono (integralProjectiveMap (W))).mp
  simp only [Category.assoc, smoothMarkingCubicLocal_projective]
  rw [← Category.assoc, ← Category.assoc, pullback.condition]

/-- The original family maps globally to its actual integral Weierstrass cubic. -/
def smoothMarkingToIntegralCubic : E.curve.left ⟶ integralCurve (W) :=
  (C).glueMorphisms (smoothMarkingCubicLocal E s e)
    (smoothMarkingCubicLocal_compatible E s e)

/-- Gluing retains the concrete local normalized morphisms. -/
@[reassoc] theorem smoothMarkingToIntegralCubic_onChart (j : Fin 3) :
    (C).f j ≫ smoothMarkingToIntegralCubic E s e =
      smoothMarkingCubicLocal E s e j :=
  (C).ι_glueMorphisms _ _ j

/-- The global morphism factors the original degree-three projective presentation. -/
@[reassoc] theorem smoothMarkingToIntegralCubic_projective :
    smoothMarkingToIntegralCubic E s e ≫ integralProjectiveMap (W) =
      smoothMarkingToProjectiveSpace E s e := by
  apply (C).hom_ext
  intro j
  rw [smoothMarkingToIntegralCubic_onChart_assoc, smoothMarkingCubicLocal_projective]

/-- The factorization preserves the original varying structural morphism. -/
@[reassoc] theorem smoothMarkingToIntegralCubic_over :
    smoothMarkingToIntegralCubic E s e ≫ integralCurveStructure (W) =
      E.curve.hom ≫ S.toSpecΓ := by
  rw [← integralProjectiveMap_baseProjection,
    smoothMarkingToIntegralCubic_projective_assoc, smoothMarkingToProjectiveSpace_over]

end FLT.Mazur.GeneralizedEllipticCurve

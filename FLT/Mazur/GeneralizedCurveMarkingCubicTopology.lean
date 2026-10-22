/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingCubicFinite
public import FLT.Mazur.WeierstrassAffineChartDense

/-!
# The relative cubic morphism on underlying spaces

Its image contains the dense affine chart and is closed by properness. The
resulting continuous closed bijection is a homeomorphism. This topological
comparison does not assert that the local rings are already isomorphic.

This specialization assumes integral geometric fibers, allowing singular cubics
but excluding higher polygons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  Scheme.Modules.pullback ModuleSheafTensor.tensor

variable {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) [GeometricallyIntegral E.curve.hom]
  (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

local instance generalizedCurveMarkingCubicTopologyProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "L" => divisorLineBundle (Scheme.Hom.ker (Over.Hom.left (t))) (hI)
local notation "T" => smoothMarkingProjectiveSections E s e
local notation "W" => smoothMarkingWeierstrassCurve E s e
open WeierstrassIntegralChart

local notation "U" => (TopologicalSpace.Closeds.compl (Scheme.IdealSheafData.support
    (Scheme.Hom.ker (Over.Hom.left (t)))) : E.curve.left.Opens)

local notation "f" => smoothMarkingToIntegralCubic E s e

/-- The image contains the entire original affine cubic chart. -/
theorem smoothMarkingToIntegralCubic_range_contains_affine :
    Set.range (integralCurveChart (W) 2) ⊆ Set.range (f) := by
  rintro _ ⟨a, rfl⟩
  let Q := smoothMarkingIntegralAffineIso E s e
  refine ⟨(Scheme.Opens.ι (X := E.curve.left) (U)) (Q.inv a), ?_⟩
  have h : Q.inv ≫ (Scheme.Opens.ι (X := E.curve.left) (U)) ≫ (f) =
      integralCurveChart (W) 2 := by
    rw [← smoothMarkingIntegralAffineIso_chart, Iso.inv_hom_id_assoc]
  exact congrArg (fun k ↦ k a) h

/-- The original cubic morphism is surjective over arbitrary original bases. -/
theorem smoothMarkingToIntegralCubic_surjective : Function.Surjective (f) := by
  let _ := smoothMarkingToIntegralCubic_proper E s e
  intro z
  exact closure_minimal (smoothMarkingToIntegralCubic_range_contains_affine E s e)
    (f).isClosedMap.isClosed_range (integralCurveAffine_denseRange (W) z)

/-- Properness and the affine/marking decomposition give a homeomorphism of underlying spaces. -/
def smoothMarkingIntegralCubicHomeomorph : E.curve.left ≃ₜ integralCurve (W) := by
  let _ := smoothMarkingToIntegralCubic_proper E s e
  exact (Equiv.ofBijective (f) ⟨smoothMarkingToIntegralCubic_injective E s e,
    smoothMarkingToIntegralCubic_surjective E s e⟩).toHomeomorphOfContinuousClosed
      (f).continuous (f).isClosedMap

/-- The homeomorphism retains the actual global cubic morphism on points. -/
theorem smoothMarkingIntegralCubicHomeomorph_apply (x : E.curve.left) :
    smoothMarkingIntegralCubicHomeomorph E s e x = (f) x := rfl

end FLT.Mazur.GeneralizedEllipticCurve

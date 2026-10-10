/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralCurveTwoChartCover
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Finite presentation of the integral cubic atlas

Every chart has three generators and two relations over the coefficient ring.
This proves local finite presentation of the glued model without a noetherian
or discriminant assumption. Its finite affine cover also proves compactness.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The two displayed chart relations form a finite generating set. -/
theorem relations_fg (j : Fin 3) : (relations W j).FG := by
  exact Submodule.fg_span (Set.toFinite _)

/-- Each actual normalized chart algebra is finitely presented over the base. -/
instance coordinate_finitePresentation (j : Fin 3) :
    Algebra.FinitePresentation R (Coordinate W j) :=
  Algebra.FinitePresentation.quotient (relations_fg W j)

/-- The affine chart structure morphisms are locally of finite presentation. -/
instance chartStructure_finitePresentation (j : Fin 3) :
    LocallyOfFinitePresentation (chartStructure W j) :=
  (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    (RingHom.finitePresentation_algebraMap.mpr inferInstance)

/-- Finite presentation descends from the explicit affine atlas. -/
instance integralCurveStructure_finitePresentation :
    LocallyOfFinitePresentation (integralCurveStructure W) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (integralCurveOpenCover W)).mpr
  intro j
  change LocallyOfFinitePresentation
    (integralCurveChart W j.down ≫ integralCurveStructure W)
  rw [integralCurveChart_structure]
  infer_instance

/-- The two actual affine charts give a compact underlying topological space. -/
instance integralCurve_compactSpace : CompactSpace (integralCurve W) := by
  let _ : Finite (integralCurveTwoChartCover W).I₀ := inferInstanceAs (Finite Bool)
  have _ (i : (integralCurveTwoChartCover W).I₀) :
      CompactSpace ((integralCurveTwoChartCover W).X i) := by
    change Bool at i
    change CompactSpace (chartScheme W (if i then 1 else 2))
    infer_instance
  exact (integralCurveTwoChartCover W).compactSpace

/-- Over the affine base, compactness makes the structure morphism quasi-compact. -/
instance integralCurveStructure_quasiCompact : QuasiCompact (integralCurveStructure W) :=
  (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance

end FLT.Mazur.WeierstrassIntegralChart

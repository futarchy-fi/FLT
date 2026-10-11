/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothTranslationChartOrbitFibers
public import FLT.Mazur.VariableHilbertChartRelationOperations

/-!
# The full chart quotient is the actual original quotient neighborhood

The orbit quotient of the full smooth chart relation is homeomorphic to its
open image in the original quotient. This identifies the concrete descent
problem on covering neighborhoods; no scheme structure is inferred merely
from a smooth scheme presentation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Smooth V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- The actual parameter map is an open quotient onto the original neighborhood. -/
theorem smoothTranslationChartToOrbit_isOpenQuotientMap :
    IsOpenQuotientMap (smoothTranslationChartToOrbit f hL d V c) :=
  ⟨smoothTranslationChartToOrbit_surjective f hL d V c,
    (smoothTranslationChartToOrbit f hL d V c).continuous,
    smoothTranslationChartToOrbit_isOpenMap f hL d V c⟩

/-- The parameter's orbit map for its full equal-class relation. -/
def variableChartOrbitProjection : C((variableHilbertTest f d V).left,
    Orbit (variableChartEquivalenceRelation f hL d V c)) :=
  ⟨projection (variableChartEquivalenceRelation f hL d V c),
    projection_continuous (variableChartEquivalenceRelation f hL d V c)⟩

omit [Smooth V.hom] in
/-- The continuous chart-orbit projection carries its actual quotient topology. -/
theorem variableChartOrbitProjection_isQuotientMap :
    IsQuotientMap (variableChartOrbitProjection f hL d V c) :=
  projection_isQuotientMap (variableChartEquivalenceRelation f hL d V c)

/-- Descend the actual parameter orbit map along its map to the original neighborhood. -/
def smoothTranslationOpenToChartOrbit : C(smoothTranslationOrbitOpen f hL d V c,
    Orbit (variableChartEquivalenceRelation f hL d V c)) :=
  (smoothTranslationChartToOrbit_isOpenQuotientMap f hL d V c).isQuotientMap.lift
    (variableChartOrbitProjection f hL d V c) (fun {x y} h ↦
      (projection_eq_iff (variableChartEquivalenceRelation f hL d V c) x y).mpr
        ((smoothTranslationChartToOrbit_eq_iff f hL d V c x y).mp h))

/-- Descend the map to the original neighborhood through the full chart relation. -/
def smoothTranslationChartOrbitToOpen :
    C(Orbit (variableChartEquivalenceRelation f hL d V c),
      smoothTranslationOrbitOpen f hL d V c) :=
  (variableChartOrbitProjection_isQuotientMap f hL d V c).lift
    (smoothTranslationChartToOrbit f hL d V c) (fun {x y} h ↦
      (smoothTranslationChartToOrbit_eq_iff f hL d V c x y).mpr
        ((projection_eq_iff (variableChartEquivalenceRelation f hL d V c) x y).mp h))

/-- The neighborhood-to-orbit comparison retains each actual parameter point. -/
theorem smoothTranslationOpenToChartOrbit_parameter (x : (variableHilbertTest f d V).left) :
    smoothTranslationOpenToChartOrbit f hL d V c (smoothTranslationChartToOrbit f hL d V c x) =
      projection (variableChartEquivalenceRelation f hL d V c) x :=
  congrArg (fun k : C(_, _) ↦ k x)
    ((smoothTranslationChartToOrbit_isOpenQuotientMap f hL d V c).isQuotientMap.lift_comp
      (variableChartOrbitProjection f hL d V c) (fun {x y} h ↦
        (projection_eq_iff (variableChartEquivalenceRelation f hL d V c) x y).mpr
          ((smoothTranslationChartToOrbit_eq_iff f hL d V c x y).mp h)))

/-- The chart-orbit comparison retains the original parameter's quotient point. -/
theorem smoothTranslationChartOrbitToOpen_projection (x : (variableHilbertTest f d V).left) :
    smoothTranslationChartOrbitToOpen f hL d V c
      (projection (variableChartEquivalenceRelation f hL d V c) x) =
        smoothTranslationChartToOrbit f hL d V c x :=
  congrArg (fun k : C(_, _) ↦ k x)
    ((variableChartOrbitProjection_isQuotientMap f hL d V c).lift_comp
      (smoothTranslationChartToOrbit f hL d V c) (fun {x y} h ↦
        (smoothTranslationChartToOrbit_eq_iff f hL d V c x y).mpr
          ((projection_eq_iff (variableChartEquivalenceRelation f hL d V c) x y).mp h)))

/-- The full chart quotient is exactly the actual open of the original quotient topologically. -/
def smoothTranslationChartOrbitHomeomorph :
    Orbit (variableChartEquivalenceRelation f hL d V c) ≃ₜ
      smoothTranslationOrbitOpen f hL d V c where
  toFun := smoothTranslationChartOrbitToOpen f hL d V c
  invFun := smoothTranslationOpenToChartOrbit f hL d V c
  left_inv z := by
    obtain ⟨x, rfl⟩ := projection_surjective (variableChartEquivalenceRelation f hL d V c) z
    rw [smoothTranslationChartOrbitToOpen_projection, smoothTranslationOpenToChartOrbit_parameter]
  right_inv z := by
    obtain ⟨x, rfl⟩ := smoothTranslationChartToOrbit_surjective f hL d V c z
    rw [smoothTranslationOpenToChartOrbit_parameter, smoothTranslationChartOrbitToOpen_projection]
  continuous_toFun := (smoothTranslationChartOrbitToOpen f hL d V c).continuous
  continuous_invFun := (smoothTranslationOpenToChartOrbit f hL d V c).continuous

end FLT.Mazur.HilbertChart

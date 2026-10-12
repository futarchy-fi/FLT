/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleHilbertCommonAmbientChart
public import FLT.Mazur.VariableHilbertAffineEnvelope

/-!
# Common ambient source neighborhoods containing entire original orbits

Every finite set of unrestricted translated parameters, and in particular
an entire original orbit, lies in one open supported in one affine ambient.
The translation coordinate remains independent. No affineness or invariance
of this source open is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) (V : Over (Spec (.of R)))
local notation "A" => allAffineAmbientCharts f

/-- The original full Hilbert coordinate of an unrestricted translated source parameter. -/
def variableFullHilbertParameter : variableHilbertTest f d V ⟶ ampleHilbertTest f d :=
  variableHilbertParameter f d V ≫ acyclicHilbertArrow f d

/-- The original source locus supported in a fixed affine ambient chart. -/
def commonAmbientSourceOpen (U : (A).Index) : (variableHilbertTest f d V).left.Opens :=
  (variableFullHilbertParameter f d V).left ⁻¹ᵁ ((A).hilbertChart d U).opensRange

/-- This support locus with the original coefficient-base morphism. -/
def commonAmbientSourceTest (U : (A).Index) : Over (Spec (.of R)) :=
  Over.mk ((commonAmbientSourceOpen f d V U).ι ≫ (variableHilbertTest f d V).hom)

/-- The actual open inclusion into the unrestricted original source. -/
def commonAmbientSourceInclusion (U : (A).Index) :
    commonAmbientSourceTest f d V U ⟶ variableHilbertTest f d V :=
  Over.homMk (commonAmbientSourceOpen f d V U).ι rfl

instance (U : (A).Index) : IsOpenImmersion (commonAmbientSourceInclusion f d V U).left :=
  inferInstanceAs (IsOpenImmersion (commonAmbientSourceOpen f d V U).ι)

/-- The original Hilbert coordinate now lands in the single constructed ambient Hilbert chart. -/
def commonAmbientSourceParameter (U : (A).Index) :
    (commonAmbientSourceTest f d V U).left ⟶ (A).hilbert d U :=
  commonAmbientChartLift f d (variableFullHilbertParameter f d V).left U

/-- The common-chart coordinate preserves the entire original Hilbert morphism. -/
@[reassoc]
theorem commonAmbientSourceParameter_fac (U : (A).Index) :
    commonAmbientSourceParameter f d V U ≫ (A).hilbertChart d U =
      (commonAmbientSourceInclusion f d V U).left ≫
        (variableFullHilbertParameter f d V).left :=
  commonAmbientChartLift_fac f d (variableFullHilbertParameter f d V).left U

/-- The single ambient chart still carries the original coefficient-base structure. -/
@[reassoc]
theorem commonAmbientSourceParameter_over (U : (A).Index) :
    commonAmbientSourceParameter f d V U ≫ (A).chartBase d U =
      (commonAmbientSourceTest f d V U).hom := by
  rw [← (A).hilbertChart_over d U, ← Category.assoc, commonAmbientSourceParameter_fac,
    Category.assoc]
  exact congrArg ((commonAmbientSourceInclusion f d V U).left ≫ ·)
    (Over.w (variableFullHilbertParameter f d V))

variable {L : X.Modules} (hL : AmpleLineBundle L)

include hL in
/-- One original source support open contains every point of a prescribed finite set. -/
theorem exists_commonAmbientSourceOpen (t : Set (variableHilbertTest f d V).left)
    (ht : t.Finite) : ∃ U : (A).Index, t ⊆ commonAmbientSourceOpen f d V U :=
  exists_common_ambient_chart_preimage f hL d (variableFullHilbertParameter f d V).left t ht

include hL in
/-- The WHOLE unrestricted orbit fits in one source open with a single affine ambient. -/
theorem exists_orbit_commonAmbientSourceOpen [IsAffine V.left] [Etale V.hom]
    (c : (relativeFppfSheaf f).obj.obj (op V)) (x : (variableHilbertTest f d V).left) :
    ∃ U : (A).Index,
      {y | projection (variableChartEquivalenceRelation f hL d V c) y =
        projection (variableChartEquivalenceRelation f hL d V c) x} ⊆
          commonAmbientSourceOpen f d V U :=
  exists_commonAmbientSourceOpen f d V hL _ (variableChartOrbit_finite f d V c hL x)

end FLT.Mazur.HilbertChart

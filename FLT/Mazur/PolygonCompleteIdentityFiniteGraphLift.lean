/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAllPositiveLaws
public import FLT.Mazur.PolygonCompleteIdentityGraphRotatedEdge
public import FLT.Mazur.PolygonInfinitesimalEdgeKernel

/-!
# Every whole finite action input lifts to the original graph closure

The proved original law constructs the ambient graph map. Its restrictions
to every full Laurent edge are the original smooth graph maps. Closed
factorization therefore retains all finite nodes and their nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "q" => completeIdentityFiniteInput K n h 0 m
local notation "f" => completeIdentityFiniteScaling K n h m
local notation "a" => completeIdentityActionTarget K n h 0
local notation "c" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "j" => completeIdentityActionGraphInclusion K n h

/-- The actual finite law gives a point of the unchanged complete lifting space. -/
def completeIdentityFiniteGraphMap :
    scalingParameterFamily (A) (t) n h ⟶ completeIdentityActionLiftSpace K n h :=
  pullback.lift (q) (f) (completeIdentityFiniteComparison_all K n h m).symm

/-- Its original input coordinate is unchanged. -/
@[reassoc] theorem completeIdentityFiniteGraphMap_fst :
    completeIdentityFiniteGraphMap K n h m ≫ pullback.fst (a) (c) = (q) :=
  pullback.lift_fst _ _ _

/-- Its target coordinate is the proved whole-stage original action. -/
@[reassoc] theorem completeIdentityFiniteGraphMap_snd :
    completeIdentityFiniteGraphMap K n h m ≫ pullback.snd (a) (c) = (f) :=
  pullback.lift_snd _ _ _

/-- Every full edge of this map is the actual original smooth graph. -/
@[reassoc] theorem completeIdentityFiniteGraphMap_edge (b : ZMod n) :
    completeIdentityRotatedEdgeToGraph K n h m b ≫ (j) =
      edge (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h (rotateIndex b 0) ≫
        completeIdentityFiniteGraphMap K n h m := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, completeIdentityFiniteGraphMap_fst]
    exact completeIdentityRotatedEdgeToGraph_source K n h m b
  · rw [Category.assoc, Category.assoc, completeIdentityFiniteGraphMap_snd]
    change completeIdentityRotatedEdgeToGraph K n h m b ≫
      completeIdentityActionGraphLift K n h = _
    rw [completeIdentityRotatedEdgeToGraph_target, completeIdentityFiniteScaling_rotatedEdge]
    simpa only [Category.assoc] using congrArg
      (fun u ↦ u ≫ (completePointIdentityOpen K n h 0).ι ≫ completeRotation K n h b)
      (completeIdentityFiniteLaw_all K n h m).symm

local instance finiteGraphCoefficients_noetherian : IsNoetherianRing (A)[T;T⁻¹] :=
  IsLocalization.isNoetherianRing (Submonoid.powers (Polynomial.X : Polynomial (A)))
    (A)[T;T⁻¹] inferInstance

local instance finiteGraphSource_noetherian :
    IsNoetherian (scheme (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h) :=
  Chow.source_isNoetherian (toBase (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h)

local instance finiteGraphNode_noetherian :
    IsNoetherian (PolygonSmoothing.chart (A)[T;T⁻¹] (LaurentPolynomial.C (t))) :=
  Chow.source_isNoetherian (PolygonSmoothing.chartStructure (A)[T;T⁻¹]
    (LaurentPolynomial.C (t)))

/-- The whole original finite input factors through the full complete graph closure. -/
def completeIdentityFiniteToGraph :
    scalingParameterFamily (A) (t) n h ⟶ completeIdentityActionGraphClosure K n h := by
  refine closedLiftOfEdges (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h (j)
    (completeIdentityFiniteGraphMap K n h m)
    (fun i ↦ completeIdentityRotatedEdgeToGraph K n h m (ZMod.finEquiv n i)) ?_
  intro i
  have hi : rotateIndex (ZMod.finEquiv n i) (0 : Fin n) = i := by
    simp only [rotateIndex, map_zero, zero_add, RingEquiv.symm_apply_apply]
  simpa only [hi] using completeIdentityFiniteGraphMap_edge K n h m (ZMod.finEquiv n i)

/-- Closed factorization retains the full ambient graph map. -/
@[reassoc] theorem completeIdentityFiniteToGraph_inclusion :
    completeIdentityFiniteToGraph K n h m ≫ (j) = completeIdentityFiniteGraphMap K n h m :=
  closedLiftOfEdges_fac _ _ _ _ _ _ _ _

/-- The original graph projection has a whole finite-input lift at every order. -/
@[reassoc] theorem completeIdentityFiniteToGraph_source :
    completeIdentityFiniteToGraph K n h m ≫ completeIdentityActionGraphProjection K n h = (q) := by
  rw [completeIdentityActionGraphProjection, completeIdentityFiniteToGraph_inclusion_assoc,
    completeIdentityFiniteGraphMap_fst]

/-- The full graph lift retains the original scaling on every finite node. -/
@[reassoc] theorem completeIdentityFiniteToGraph_target :
    completeIdentityFiniteToGraph K n h m ≫ completeIdentityActionGraphLift K n h = (f) := by
  rw [completeIdentityActionGraphLift, completeIdentityFiniteToGraph_inclusion_assoc,
    completeIdentityFiniteGraphMap_snd]

end FLT.Mazur.PolygonInfinitesimalStages

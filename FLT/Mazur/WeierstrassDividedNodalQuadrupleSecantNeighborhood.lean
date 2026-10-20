/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSecantBranchNeighborhood
public import FLT.Mazur.WeierstrassDividedNodalQuadrupleSecantContraction

/-!
# Smooth quadruple-depth branch neighborhoods in the original secant source

Both strict branches now have actual common neighborhoods in the original
ordered secant source. Their outputs land in the same resolved smooth locus
and contract to the exact original secant, while retaining the input maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
  nodalBranchCommonOutput nodalNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k : ℕ} (D : SplitNodeDepth W π (4 * k))
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "σ" => nodalSecondShear D k
local notation "a'" => branchNegativeInput W s d.b3 d.b4 d.b6 a
local notation "c'" => branchNegativeInput W s d.b3 d.b4 d.b6 c
local notation "T" => DividedSecantRing W s d.b3 d.b4 d.b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ (splitNodeDoubledFamily D) (k + k) le_rfl
local notation "U" => (base).smoothLocus

/-- The two original branch sources: true is complementary, false is swapped. -/
def nodalQuadrupleSecantBranchSource : Bool → Scheme
  | true => Spec (.of (DividedShearBranchOverlap W s d.b3 d.b4 d.b6 σ a' c'))
  | false => Spec (.of (DividedShearBranchOverlap W s d.b3 d.b4 d.b6 σ c a))

/-- Each branch uses the original source algebra of the same ordered input pair. -/
def nodalQuadrupleSecantBranchInclusion (i : Bool) :
    nodalQuadrupleSecantBranchSource D d a c i ⟶ Spec (.of S) :=
  match i with
  | true => dividedShearBranchInclusion W s d.b3 d.b4 d.b6 σ a' c'
  | false => dividedShearBranchInclusion W s d.b3 d.b4 d.b6 σ c a

instance nodalQuadrupleSecantBranchInclusion_open (i : Bool) :
    IsOpenImmersion (nodalQuadrupleSecantBranchInclusion D d a c i) := by
  cases i <;> exact dividedShearBranchInclusion_open ..

/-- Both actual outputs take values in the same original finite model. -/
def nodalQuadrupleSecantBranchOutput (i : Bool) :
    nodalQuadrupleSecantBranchSource D d a c i ⟶
      finiteGlobalModel hπ (splitNodeDoubledFamily D) (k + k) le_rfl :=
  match i with
  | true => nodalNegativeBranchOutput D d a c
  | false => nodalBranchCommonOutput D d c a

/-- On any common scheme, either branch contracts to the original ordered secant. -/
theorem nodalQuadrupleSecantBranchOutput_contraction (i : Bool) {X : Scheme}
    (p : X ⟶ nodalQuadrupleSecantBranchSource D d a c i) (q : X ⟶ Spec (.of T))
    (hpq : p ≫ nodalQuadrupleSecantBranchInclusion D d a c i = q ≫ t) :
    p ≫ nodalQuadrupleSecantBranchOutput D d a c i ≫
        finiteGlobalContraction hπ (splitNodeDoubledFamily D) (k + k) le_rfl =
      q ≫ dividedSecantToCurve W s d.b3 d.b4 d.b6 a c
        d.factor3 d.factor4 d.factor6 := by
  cases i with
  | false =>
    exact nodalSwappedBranchOutput_secant_contraction
      D d a c p q hpq
  | true =>
    exact nodalNegativeBranchOutput_secant_contraction
      D d a c p q hpq

variable [IsNoetherianRing R]

local notation "j" => nodalQuadrupleSecantBranchInclusion D d a c
local notation "f" => nodalQuadrupleSecantBranchOutput D d a c

/-- The common branch domain, restricted to smooth outputs, inside the original secant. -/
def nodalQuadrupleSecantNeighborhood (i : Bool) : Scheme :=
  secantBranchNeighborhood t (j i) (f i) U

/-- The genuine open inclusion into the original secant source. -/
def nodalQuadrupleSecantNeighborhoodInclusion (i : Bool) :
    nodalQuadrupleSecantNeighborhood D d a c i ⟶ Spec (.of T) :=
  secantBranchNeighborhoodInclusion t (j i) (f i) U

instance nodalQuadrupleSecantNeighborhoodInclusion_open (i : Bool) :
    IsOpenImmersion
      (nodalQuadrupleSecantNeighborhoodInclusion D d a c i) := by
  unfold nodalQuadrupleSecantNeighborhoodInclusion
  infer_instance

/-- The neighborhood's actual output in the smooth locus of the same finite model. -/
def nodalQuadrupleSecantNeighborhoodOutput (i : Bool) :
    nodalQuadrupleSecantNeighborhood D d a c i ⟶ (U).toScheme :=
  secantBranchNeighborhoodOutput t (j i) (f i) U

/-- The complete neighborhood output contracts to the original ordered secant formula. -/
@[reassoc] theorem nodalQuadrupleSecantNeighborhoodOutput_contraction (i : Bool) :
    nodalQuadrupleSecantNeighborhoodOutput D d a c i ≫ (U).ι ≫
        finiteGlobalContraction hπ (splitNodeDoubledFamily D) (k + k) le_rfl =
      nodalQuadrupleSecantNeighborhoodInclusion D d a c i ≫
        dividedSecantToCurve W s d.b3 d.b4 d.b6 a c
          d.factor3 d.factor4 d.factor6 := by
  rw [nodalQuadrupleSecantNeighborhoodOutput, secantBranchNeighborhoodOutput_inclusion_assoc]
  exact nodalQuadrupleSecantBranchOutput_contraction D d a c i _ _
    (secantBranchNeighborhood_source t (j i) (f i) U)

/-- Both input functions remain the original ordered input functions on each neighborhood. -/
theorem nodalQuadrupleSecantNeighborhood_input (i : Bool)
    (b : Coordinate W s d.b3 d.b4 d.b6 →ₐ[R] S) :
    secantBranchNeighborhoodBranch t (j i) (f i) U ≫ j i ≫
        Spec.map (CommRingCat.ofHom b.toRingHom) =
      nodalQuadrupleSecantNeighborhoodInclusion D d a c i ≫ t ≫
        Spec.map (CommRingCat.ofHom b.toRingHom) :=
  secantBranchNeighborhood_input t (j i) (f i) U _

/-- The neighborhood output retains the coefficient structure of the original secant. -/
@[reassoc] theorem nodalQuadrupleSecantNeighborhoodOutput_structure (i : Bool) :
    nodalQuadrupleSecantNeighborhoodOutput D d a c i ≫ (U).ι ≫ base =
      nodalQuadrupleSecantNeighborhoodInclusion D d a c i ≫
        Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  change _ ≫ (U).ι ≫ finiteGlobalContraction hπ (splitNodeDoubledFamily D) (k + k) le_rfl ≫
    WeierstrassIntegralChart.integralCurveStructure W = _
  rw [nodalQuadrupleSecantNeighborhoodOutput_contraction_assoc, dividedSecantToCurve_structure]

end FLT.Mazur.WeierstrassDividedDepth

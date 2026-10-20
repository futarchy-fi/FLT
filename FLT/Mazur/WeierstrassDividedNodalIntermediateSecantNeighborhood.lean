/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSecantBranchNeighborhood
public import FLT.Mazur.WeierstrassDividedNodalIntermediateSecantContraction

/-!
# Smooth intermediate-depth branch neighborhoods in the original secant source

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
  nodalIntermediateBranchCommonOutput nodalIntermediateNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m r : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 3 * k ≤ m) (hrk : r ≤ k) (hrm : r ≤ m - 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : k + r ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "σ" => nodalSecondShear D k
local notation "a'" => branchNegativeInput W s d.b3 d.b4 d.b6 a
local notation "c'" => branchNegativeInput W s d.b3 d.b4 d.b6 c
local notation "T" => DividedSecantRing W s d.b3 d.b4 d.b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ (start := 0) data (k + r) hj
local notation "U" => (base).smoothLocus

/-- The two original branch sources: true is complementary, false is swapped. -/
def nodalIntermediateSecantBranchSource : Bool → Scheme
  | true => Spec (.of (DividedShearBranchOverlap W s d.b3 d.b4 d.b6 σ a' c'))
  | false => Spec (.of (DividedShearBranchOverlap W s d.b3 d.b4 d.b6 σ c a))

/-- Each branch uses the original source algebra of the same ordered input pair. -/
def nodalIntermediateSecantBranchInclusion (i : Bool) :
    nodalIntermediateSecantBranchSource D d a c i ⟶ Spec (.of S) :=
  match i with
  | true => dividedShearBranchInclusion W s d.b3 d.b4 d.b6 σ a' c'
  | false => dividedShearBranchInclusion W s d.b3 d.b4 d.b6 σ c a

instance nodalIntermediateSecantBranchInclusion_open (i : Bool) :
    IsOpenImmersion (nodalIntermediateSecantBranchInclusion D d a c i) := by
  cases i <;> exact dividedShearBranchInclusion_open ..

/-- Both actual outputs take values in the same original finite model. -/
def nodalIntermediateSecantBranchOutput (i : Bool) :
    nodalIntermediateSecantBranchSource D d a c i ⟶
      finiteGlobalModel hπ (start := 0) data (k + r) hj :=
  match i with
  | true => nodalIntermediateNegativeBranchOutput D hdepth hrk hrm data hj d a c
  | false => nodalIntermediateBranchCommonOutput D hdepth hrk hrm data hj d c a

/-- On any common scheme, either branch contracts to the original ordered secant. -/
theorem nodalIntermediateSecantBranchOutput_contraction (i : Bool) {X : Scheme}
    (p : X ⟶ nodalIntermediateSecantBranchSource D d a c i) (q : X ⟶ Spec (.of T))
    (hpq : p ≫ nodalIntermediateSecantBranchInclusion D d a c i = q ≫ t) :
    p ≫ nodalIntermediateSecantBranchOutput D hdepth hrk hrm data hj d a c i ≫
        finiteGlobalContraction hπ (start := 0) data (k + r) hj =
      q ≫ dividedSecantToCurve W s d.b3 d.b4 d.b6 a c
        d.factor3 d.factor4 d.factor6 := by
  cases i with
  | false =>
    exact nodalIntermediateSwappedBranchOutput_secant_contraction
      D hdepth hrk hrm data hj d a c p q hpq
  | true =>
    exact nodalIntermediateNegativeBranchOutput_secant_contraction
      D hdepth hrk hrm data hj d a c p q hpq

variable [IsNoetherianRing R]

local notation "j" => nodalIntermediateSecantBranchInclusion D d a c
local notation "f" => nodalIntermediateSecantBranchOutput D hdepth hrk hrm data hj d a c

/-- The common branch domain, restricted to smooth outputs, inside the original secant. -/
def nodalIntermediateSecantNeighborhood (i : Bool) : Scheme :=
  secantBranchNeighborhood t (j i) (f i) U

/-- The genuine open inclusion into the original secant source. -/
def nodalIntermediateSecantNeighborhoodInclusion (i : Bool) :
    nodalIntermediateSecantNeighborhood D hdepth hrk hrm data hj d a c i ⟶ Spec (.of T) :=
  secantBranchNeighborhoodInclusion t (j i) (f i) U

instance nodalIntermediateSecantNeighborhoodInclusion_open (i : Bool) :
    IsOpenImmersion
      (nodalIntermediateSecantNeighborhoodInclusion D hdepth hrk hrm data hj d a c i) := by
  unfold nodalIntermediateSecantNeighborhoodInclusion
  infer_instance

/-- The neighborhood's actual output in the smooth locus of the same finite model. -/
def nodalIntermediateSecantNeighborhoodOutput (i : Bool) :
    nodalIntermediateSecantNeighborhood D hdepth hrk hrm data hj d a c i ⟶ (U).toScheme :=
  secantBranchNeighborhoodOutput t (j i) (f i) U

/-- The complete neighborhood output contracts to the original ordered secant formula. -/
@[reassoc] theorem nodalIntermediateSecantNeighborhoodOutput_contraction (i : Bool) :
    nodalIntermediateSecantNeighborhoodOutput D hdepth hrk hrm data hj d a c i ≫ (U).ι ≫
        finiteGlobalContraction hπ (start := 0) data (k + r) hj =
      nodalIntermediateSecantNeighborhoodInclusion D hdepth hrk hrm data hj d a c i ≫
        dividedSecantToCurve W s d.b3 d.b4 d.b6 a c
          d.factor3 d.factor4 d.factor6 := by
  rw [nodalIntermediateSecantNeighborhoodOutput, secantBranchNeighborhoodOutput_inclusion_assoc]
  exact nodalIntermediateSecantBranchOutput_contraction D hdepth hrk hrm data hj d a c i _ _
    (secantBranchNeighborhood_source t (j i) (f i) U)

/-- Both input functions remain the original ordered input functions on each neighborhood. -/
theorem nodalIntermediateSecantNeighborhood_input (i : Bool)
    (b : Coordinate W s d.b3 d.b4 d.b6 →ₐ[R] S) :
    secantBranchNeighborhoodBranch t (j i) (f i) U ≫ j i ≫
        Spec.map (CommRingCat.ofHom b.toRingHom) =
      nodalIntermediateSecantNeighborhoodInclusion D hdepth hrk hrm data hj d a c i ≫ t ≫
        Spec.map (CommRingCat.ofHom b.toRingHom) :=
  secantBranchNeighborhood_input t (j i) (f i) U _

/-- The neighborhood output retains the coefficient structure of the original secant. -/
@[reassoc] theorem nodalIntermediateSecantNeighborhoodOutput_structure (i : Bool) :
    nodalIntermediateSecantNeighborhoodOutput D hdepth hrk hrm data hj d a c i ≫ (U).ι ≫ base =
      nodalIntermediateSecantNeighborhoodInclusion D hdepth hrk hrm data hj d a c i ≫
        Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  change _ ≫ (U).ι ≫ finiteGlobalContraction hπ (start := 0) data (k + r) hj ≫
    WeierstrassIntegralChart.integralCurveStructure W = _
  rw [nodalIntermediateSecantNeighborhoodOutput_contraction_assoc, dividedSecantToCurve_structure]

end FLT.Mazur.WeierstrassDividedDepth

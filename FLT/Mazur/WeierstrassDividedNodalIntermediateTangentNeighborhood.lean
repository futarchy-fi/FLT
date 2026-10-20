/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSecantBranchNeighborhood
public import FLT.Mazur.WeierstrassDividedNodalIntermediateNegativeBranchContraction
public import FLT.Mazur.WeierstrassDividedNodalIntermediateTangentCoverage

/-!
# Smooth intermediate-depth branch neighborhoods in the original tangent source

Both strict branches now have actual common neighborhoods in the original
ordered tangent source. Their outputs land in the same resolved smooth locus
and contract to the exact original tangent, while retaining the input maps.
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
local notation "T" => DividedTangentRing W s d.b3 d.b4 d.b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ (start := 0) data (k + r) hj
local notation "U" => (base).smoothLocus

/-- The two original branch sources: true is complementary, false is swapped. -/
def nodalIntermediateTangentBranchSource : Bool → Scheme
  | true => Spec (.of (DividedShearBranchOverlap W s d.b3 d.b4 d.b6 σ a' c'))
  | false => Spec (.of (DividedShearBranchOverlap W s d.b3 d.b4 d.b6 σ c a))

/-- Each branch uses the original source algebra of the same ordered input pair. -/
def nodalIntermediateTangentBranchInclusion (i : Bool) :
    nodalIntermediateTangentBranchSource D d a c i ⟶ Spec (.of S) :=
  match i with
  | true => dividedShearBranchInclusion W s d.b3 d.b4 d.b6 σ a' c'
  | false => dividedShearBranchInclusion W s d.b3 d.b4 d.b6 σ c a

instance nodalIntermediateTangentBranchInclusion_open (i : Bool) :
    IsOpenImmersion (nodalIntermediateTangentBranchInclusion D d a c i) := by
  cases i <;> exact dividedShearBranchInclusion_open ..

/-- Both actual outputs take values in the same original finite model. -/
def nodalIntermediateTangentBranchOutput (i : Bool) :
    nodalIntermediateTangentBranchSource D d a c i ⟶
      finiteGlobalModel hπ (start := 0) data (k + r) hj :=
  match i with
  | true => nodalIntermediateNegativeBranchOutput D hdepth hrk hrm data hj d a c
  | false => nodalIntermediateBranchCommonOutput D hdepth hrk hrm data hj d c a

/-- On any common scheme, either branch contracts to the original ordered tangent. -/
theorem nodalIntermediateTangentBranchOutput_contraction (i : Bool) {X : Scheme}
    (p : X ⟶ nodalIntermediateTangentBranchSource D d a c i) (q : X ⟶ Spec (.of T))
    (hpq : p ≫ nodalIntermediateTangentBranchInclusion D d a c i = q ≫ t) :
    p ≫ nodalIntermediateTangentBranchOutput D hdepth hrk hrm data hj d a c i ≫
        finiteGlobalContraction hπ (start := 0) data (k + r) hj =
      q ≫ dividedTangentToCurve W s d.b3 d.b4 d.b6 a c
        d.factor3 d.factor4 d.factor6 := by
  cases i with
  | false =>
    exact nodalIntermediateSwappedBranchOutput_original_contraction
      D hdepth hrk hrm data hj d a c p q hpq
  | true =>
    exact nodalIntermediateNegativeBranchOutput_original_contraction
      D hdepth hrk hrm data hj d a c p q hpq

variable [IsNoetherianRing R]

local notation "j" => nodalIntermediateTangentBranchInclusion D d a c
local notation "f" => nodalIntermediateTangentBranchOutput D hdepth hrk hrm data hj d a c

/-- The common branch domain, restricted to smooth outputs, inside the original tangent. -/
def nodalIntermediateTangentNeighborhood (i : Bool) : Scheme :=
  secantBranchNeighborhood t (j i) (f i) U

/-- The genuine open inclusion into the original tangent source. -/
def nodalIntermediateTangentNeighborhoodInclusion (i : Bool) :
    nodalIntermediateTangentNeighborhood D hdepth hrk hrm data hj d a c i ⟶ Spec (.of T) :=
  secantBranchNeighborhoodInclusion t (j i) (f i) U

instance nodalIntermediateTangentNeighborhoodInclusion_open (i : Bool) :
    IsOpenImmersion
      (nodalIntermediateTangentNeighborhoodInclusion D hdepth hrk hrm data hj d a c i) := by
  unfold nodalIntermediateTangentNeighborhoodInclusion
  infer_instance

/-- The neighborhood's actual output in the smooth locus of the same finite model. -/
def nodalIntermediateTangentNeighborhoodOutput (i : Bool) :
    nodalIntermediateTangentNeighborhood D hdepth hrk hrm data hj d a c i ⟶ (U).toScheme :=
  secantBranchNeighborhoodOutput t (j i) (f i) U

/-- The complete neighborhood output contracts to the original ordered tangent formula. -/
@[reassoc] theorem nodalIntermediateTangentNeighborhoodOutput_contraction (i : Bool) :
    nodalIntermediateTangentNeighborhoodOutput D hdepth hrk hrm data hj d a c i ≫ (U).ι ≫
        finiteGlobalContraction hπ (start := 0) data (k + r) hj =
      nodalIntermediateTangentNeighborhoodInclusion D hdepth hrk hrm data hj d a c i ≫
        dividedTangentToCurve W s d.b3 d.b4 d.b6 a c
          d.factor3 d.factor4 d.factor6 := by
  rw [nodalIntermediateTangentNeighborhoodOutput, secantBranchNeighborhoodOutput_inclusion_assoc]
  exact nodalIntermediateTangentBranchOutput_contraction D hdepth hrk hrm data hj d a c i _ _
    (secantBranchNeighborhood_source t (j i) (f i) U)

/-- Both input functions remain the original ordered input functions on each neighborhood. -/
theorem nodalIntermediateTangentNeighborhood_input (i : Bool)
    (b : Coordinate W s d.b3 d.b4 d.b6 →ₐ[R] S) :
    secantBranchNeighborhoodBranch t (j i) (f i) U ≫ j i ≫
        Spec.map (CommRingCat.ofHom b.toRingHom) =
      nodalIntermediateTangentNeighborhoodInclusion D hdepth hrk hrm data hj d a c i ≫ t ≫
        Spec.map (CommRingCat.ofHom b.toRingHom) :=
  secantBranchNeighborhood_input t (j i) (f i) U _

/-- The neighborhood output retains the coefficient structure of the original tangent. -/
@[reassoc] theorem nodalIntermediateTangentNeighborhoodOutput_structure (i : Bool) :
    nodalIntermediateTangentNeighborhoodOutput D hdepth hrk hrm data hj d a c i ≫ (U).ι ≫ base =
      nodalIntermediateTangentNeighborhoodInclusion D hdepth hrk hrm data hj d a c i ≫
        Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  change _ ≫ (U).ι ≫ finiteGlobalContraction hπ (start := 0) data (k + r) hj ≫
    WeierstrassIntegralChart.integralCurveStructure W = _
  rw [nodalIntermediateTangentNeighborhoodOutput_contraction_assoc, dividedTangentToCurve_structure]

end FLT.Mazur.WeierstrassDividedDepth

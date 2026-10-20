/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSecantBranchNeighborhood
public import FLT.Mazur.WeierstrassDividedNodalShallowNegativeBranchContraction
public import FLT.Mazur.WeierstrassDividedNodalShallowTangentCoverage

/-!
# Smooth shallow-depth branch neighborhoods in the original tangent source

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
  nodalShallowBranchCommonOutput nodalShallowNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 2 * k ≤ m) (hm : m ≤ 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : m - 2 * k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "σ" => nodalSecondShear D k
local notation "a'" => branchNegativeInput W s d.b3 d.b4 d.b6 a
local notation "c'" => branchNegativeInput W s d.b3 d.b4 d.b6 c
local notation "T" => DividedTangentRing W s d.b3 d.b4 d.b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ (start := 0) data (m - 2 * k) hj
local notation "U" => (base).smoothLocus

/-- The two original branch sources: true is complementary, false is swapped. -/
def nodalShallowTangentBranchSource : Bool → Scheme
  | true => Spec (.of (DividedShearBranchOverlap W s d.b3 d.b4 d.b6 σ a' c'))
  | false => Spec (.of (DividedShearBranchOverlap W s d.b3 d.b4 d.b6 σ c a))

/-- Each branch uses the original source algebra of the same ordered input pair. -/
def nodalShallowTangentBranchInclusion (i : Bool) :
    nodalShallowTangentBranchSource D d a c i ⟶ Spec (.of S) :=
  match i with
  | true => dividedShearBranchInclusion W s d.b3 d.b4 d.b6 σ a' c'
  | false => dividedShearBranchInclusion W s d.b3 d.b4 d.b6 σ c a

instance nodalShallowTangentBranchInclusion_open (i : Bool) :
    IsOpenImmersion (nodalShallowTangentBranchInclusion D d a c i) := by
  cases i <;> exact dividedShearBranchInclusion_open ..

/-- Both actual outputs take values in the same original finite model. -/
def nodalShallowTangentBranchOutput (i : Bool) :
    nodalShallowTangentBranchSource D d a c i ⟶
      finiteGlobalModel hπ (start := 0) data (m - 2 * k) hj :=
  match i with
  | true => nodalShallowNegativeBranchOutput D hdepth hm data hj d a c
  | false => nodalShallowBranchCommonOutput D hdepth hm data hj d c a

/-- On any common scheme, either branch contracts to the original ordered tangent. -/
theorem nodalShallowTangentBranchOutput_contraction (i : Bool) {X : Scheme}
    (p : X ⟶ nodalShallowTangentBranchSource D d a c i) (q : X ⟶ Spec (.of T))
    (hpq : p ≫ nodalShallowTangentBranchInclusion D d a c i = q ≫ t) :
    p ≫ nodalShallowTangentBranchOutput D hdepth hm data hj d a c i ≫
        finiteGlobalContraction hπ (start := 0) data (m - 2 * k) hj =
      q ≫ dividedTangentToCurve W s d.b3 d.b4 d.b6 a c
        d.factor3 d.factor4 d.factor6 := by
  cases i with
  | false =>
    exact nodalShallowSwappedBranchOutput_original_contraction
      D hdepth hm data hj d a c p q hpq
  | true =>
    exact nodalShallowNegativeBranchOutput_original_contraction
      D hdepth hm data hj d a c p q hpq

variable [IsNoetherianRing R]

local notation "j" => nodalShallowTangentBranchInclusion D d a c
local notation "f" => nodalShallowTangentBranchOutput D hdepth hm data hj d a c

/-- The common branch domain, restricted to smooth outputs, inside the original tangent. -/
def nodalShallowTangentNeighborhood (i : Bool) : Scheme :=
  secantBranchNeighborhood t (j i) (f i) U

/-- The genuine open inclusion into the original tangent source. -/
def nodalShallowTangentNeighborhoodInclusion (i : Bool) :
    nodalShallowTangentNeighborhood D hdepth hm data hj d a c i ⟶ Spec (.of T) :=
  secantBranchNeighborhoodInclusion t (j i) (f i) U

instance nodalShallowTangentNeighborhoodInclusion_open (i : Bool) :
    IsOpenImmersion
      (nodalShallowTangentNeighborhoodInclusion D hdepth hm data hj d a c i) := by
  unfold nodalShallowTangentNeighborhoodInclusion
  infer_instance

/-- The neighborhood's actual output in the smooth locus of the same finite model. -/
def nodalShallowTangentNeighborhoodOutput (i : Bool) :
    nodalShallowTangentNeighborhood D hdepth hm data hj d a c i ⟶ (U).toScheme :=
  secantBranchNeighborhoodOutput t (j i) (f i) U

/-- The complete neighborhood output contracts to the original ordered tangent formula. -/
@[reassoc] theorem nodalShallowTangentNeighborhoodOutput_contraction (i : Bool) :
    nodalShallowTangentNeighborhoodOutput D hdepth hm data hj d a c i ≫ (U).ι ≫
        finiteGlobalContraction hπ (start := 0) data (m - 2 * k) hj =
      nodalShallowTangentNeighborhoodInclusion D hdepth hm data hj d a c i ≫
        dividedTangentToCurve W s d.b3 d.b4 d.b6 a c
          d.factor3 d.factor4 d.factor6 := by
  rw [nodalShallowTangentNeighborhoodOutput, secantBranchNeighborhoodOutput_inclusion_assoc]
  exact nodalShallowTangentBranchOutput_contraction D hdepth hm data hj d a c i _ _
    (secantBranchNeighborhood_source t (j i) (f i) U)

/-- Both input functions remain the original ordered input functions on each neighborhood. -/
theorem nodalShallowTangentNeighborhood_input (i : Bool)
    (b : Coordinate W s d.b3 d.b4 d.b6 →ₐ[R] S) :
    secantBranchNeighborhoodBranch t (j i) (f i) U ≫ j i ≫
        Spec.map (CommRingCat.ofHom b.toRingHom) =
      nodalShallowTangentNeighborhoodInclusion D hdepth hm data hj d a c i ≫ t ≫
        Spec.map (CommRingCat.ofHom b.toRingHom) :=
  secantBranchNeighborhood_input t (j i) (f i) U _

/-- The neighborhood output retains the coefficient structure of the original tangent. -/
@[reassoc] theorem nodalShallowTangentNeighborhoodOutput_structure (i : Bool) :
    nodalShallowTangentNeighborhoodOutput D hdepth hm data hj d a c i ≫ (U).ι ≫ base =
      nodalShallowTangentNeighborhoodInclusion D hdepth hm data hj d a c i ≫
        Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  change _ ≫ (U).ι ≫ finiteGlobalContraction hπ (start := 0) data (m - 2 * k) hj ≫
    WeierstrassIntegralChart.integralCurveStructure W = _
  rw [nodalShallowTangentNeighborhoodOutput_contraction_assoc, dividedTangentToCurve_structure]

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalDeepSecantNeighborhood
public import FLT.Mazur.WeierstrassDividedDeepNodalNegativeBranchContraction
public import FLT.Mazur.WeierstrassDividedDeepNodalTangentBranchCoverage

/-!
# Smooth deep-node branch neighborhoods in the original tangent source

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
  deepNodalBranchCommonOutput deepNodalNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k n m : ℕ} (D : SplitNodeDepth W π m)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : k + k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "r" => nodalSecondShear D k
local notation "a'" => branchNegativeInput W s d.b3 d.b4 d.b6 a
local notation "c'" => branchNegativeInput W s d.b3 d.b4 d.b6 c
local notation "T" => DividedTangentRing W s d.b3 d.b4 d.b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data (k + k) hj
local notation "U" => (base).smoothLocus

/-- On any common scheme, either branch contracts to the original ordered tangent. -/
theorem deepNodalTangentBranchOutput_contraction (i : Bool) {X : Scheme}
    (p : X ⟶ nodalDeepSecantBranchSource D d a c i) (q : X ⟶ Spec (.of T))
    (hpq : p ≫ nodalDeepSecantBranchInclusion D d a c i = q ≫ t) :
    p ≫ nodalDeepSecantBranchOutput D data hj d a c i ≫
        finiteGlobalContraction hπ data (k + k) hj =
      q ≫ dividedTangentToCurve W s d.b3 d.b4 d.b6 a c
        d.factor3 d.factor4 d.factor6 := by
  cases i with
  | false => exact deepNodalSwappedBranchOutput_original_contraction D data hj d a c p q hpq
  | true => exact deepNodalNegativeBranchOutput_original_contraction D data hj d a c p q hpq

variable [IsNoetherianRing R]

local notation "j" => nodalDeepSecantBranchInclusion D d a c
local notation "f" => nodalDeepSecantBranchOutput D data hj d a c

/-- The common branch domain, restricted to smooth outputs, inside the original tangent. -/
def deepNodalTangentNeighborhood (i : Bool) : Scheme :=
  secantBranchNeighborhood t (j i) (f i) U

/-- The genuine open inclusion into the original tangent source. -/
def deepNodalTangentNeighborhoodInclusion (i : Bool) :
    deepNodalTangentNeighborhood D data hj d a c i ⟶ Spec (.of T) :=
  secantBranchNeighborhoodInclusion t (j i) (f i) U

instance deepNodalTangentNeighborhoodInclusion_open (i : Bool) :
    IsOpenImmersion (deepNodalTangentNeighborhoodInclusion D data hj d a c i) := by
  unfold deepNodalTangentNeighborhoodInclusion
  infer_instance

/-- The neighborhood's actual output in the smooth locus of the same finite model. -/
def deepNodalTangentNeighborhoodOutput (i : Bool) :
    deepNodalTangentNeighborhood D data hj d a c i ⟶ (U).toScheme :=
  secantBranchNeighborhoodOutput t (j i) (f i) U

/-- The complete neighborhood output contracts to the original ordered tangent formula. -/
@[reassoc] theorem deepNodalTangentNeighborhoodOutput_contraction (i : Bool) :
    deepNodalTangentNeighborhoodOutput D data hj d a c i ≫ (U).ι ≫
        finiteGlobalContraction hπ data (k + k) hj =
      deepNodalTangentNeighborhoodInclusion D data hj d a c i ≫
        dividedTangentToCurve W s d.b3 d.b4 d.b6 a c
          d.factor3 d.factor4 d.factor6 := by
  rw [deepNodalTangentNeighborhoodOutput, secantBranchNeighborhoodOutput_inclusion_assoc]
  exact deepNodalTangentBranchOutput_contraction D data hj d a c i _ _
    (secantBranchNeighborhood_source t (j i) (f i) U)

/-- Both input functions remain the original ordered input functions on each neighborhood. -/
theorem deepNodalTangentNeighborhood_input (i : Bool)
    (b : Coordinate W s d.b3 d.b4 d.b6 →ₐ[R] S) :
    secantBranchNeighborhoodBranch t (j i) (f i) U ≫ j i ≫
        Spec.map (CommRingCat.ofHom b.toRingHom) =
      deepNodalTangentNeighborhoodInclusion D data hj d a c i ≫ t ≫
        Spec.map (CommRingCat.ofHom b.toRingHom) :=
  secantBranchNeighborhood_input t (j i) (f i) U _

/-- The neighborhood output retains the coefficient structure of the original tangent. -/
@[reassoc] theorem deepNodalTangentNeighborhoodOutput_structure (i : Bool) :
    deepNodalTangentNeighborhoodOutput D data hj d a c i ≫ (U).ι ≫ base =
      deepNodalTangentNeighborhoodInclusion D data hj d a c i ≫
        Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  change _ ≫ (U).ι ≫ finiteGlobalContraction hπ data (k + k) hj ≫
    WeierstrassIntegralChart.integralCurveStructure W = _
  rw [deepNodalTangentNeighborhoodOutput_contraction_assoc, dividedTangentToCurve_structure]

end FLT.Mazur.WeierstrassDividedDepth

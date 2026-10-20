/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSecantBranchNeighborhood
public import FLT.Mazur.WeierstrassDividedTripleNegativeBranchContraction
public import FLT.Mazur.WeierstrassDividedTripleTangentBranchCoverage

/-!
# Smooth exact-triple branch neighborhoods in the original tangent source

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
  tripleBranchCommonOutput tripleNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {start n k : ℕ}
  (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (a c : Coordinate W (π ^ (start + k))
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b3 (data ⟨k, Nat.lt_succ_of_le hk⟩).b4
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b6 →ₐ[R] S)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
local notation "s" => π ^ (start + k)
local notation "σ" => nodalSecondShear D (start + k)
local notation "a'" => branchNegativeInput W s (d).b3 (d).b4 (d).b6 a
local notation "c'" => branchNegativeInput W s (d).b3 (d).b4 (d).b6 c
local notation "T" => DividedTangentRing W s (d).b3 (d).b4 (d).b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "U" => (base).smoothLocus

/-- The two original branch sources: true is complementary, false is swapped. -/
def tripleTangentBranchSource : Bool → Scheme
  | true => Spec (.of (DividedShearBranchOverlap W s (d).b3 (d).b4 (d).b6 σ a' c'))
  | false => Spec (.of (DividedShearBranchOverlap W s (d).b3 (d).b4 (d).b6 σ c a))

/-- Each branch uses the original source algebra of the same ordered input pair. -/
def tripleTangentBranchInclusion (i : Bool) :
    tripleTangentBranchSource D data hk a c i ⟶ Spec (.of S) :=
  match i with
  | true => dividedShearBranchInclusion W s (d).b3 (d).b4 (d).b6 σ a' c'
  | false => dividedShearBranchInclusion W s (d).b3 (d).b4 (d).b6 σ c a

instance tripleTangentBranchInclusion_open (i : Bool) :
    IsOpenImmersion (tripleTangentBranchInclusion D data hk a c i) := by
  cases i <;> exact dividedShearBranchInclusion_open ..

/-- Both actual outputs take values in the same original finite model. -/
def tripleTangentBranchOutput (i : Bool) :
    tripleTangentBranchSource D data hk a c i ⟶
      finiteGlobalModel hπ data k hk :=
  match i with
  | true => tripleNegativeBranchOutput D data hk a c
  | false => tripleBranchCommonOutput D data hk c a

/-- On any common scheme, either branch contracts to the original ordered tangent. -/
theorem tripleTangentBranchOutput_contraction (i : Bool) {X : Scheme}
    (p : X ⟶ tripleTangentBranchSource D data hk a c i) (q : X ⟶ Spec (.of T))
    (hpq : p ≫ tripleTangentBranchInclusion D data hk a c i = q ≫ t) :
    p ≫ tripleTangentBranchOutput D data hk a c i ≫
        finiteGlobalContraction hπ data k hk =
      q ≫ dividedTangentToCurve W s (d).b3 (d).b4 (d).b6 a c
        (d).factor3 (d).factor4 (d).factor6 := by
  cases i with
  | false =>
    exact tripleSwappedBranchOutput_original_contraction
      D data hk a c p q hpq
  | true =>
    exact tripleNegativeBranchOutput_original_contraction
      D data hk a c p q hpq

variable [IsNoetherianRing R]

local notation "j" => tripleTangentBranchInclusion D data hk a c
local notation "f" => tripleTangentBranchOutput D data hk a c

/-- The common branch domain, restricted to smooth outputs, inside the original tangent. -/
def tripleTangentNeighborhood (i : Bool) : Scheme :=
  secantBranchNeighborhood t (j i) (f i) U

/-- The genuine open inclusion into the original tangent source. -/
def tripleTangentNeighborhoodInclusion (i : Bool) :
    tripleTangentNeighborhood D data hk a c i ⟶ Spec (.of T) :=
  secantBranchNeighborhoodInclusion t (j i) (f i) U

instance tripleTangentNeighborhoodInclusion_open (i : Bool) :
    IsOpenImmersion
      (tripleTangentNeighborhoodInclusion D data hk a c i) := by
  unfold tripleTangentNeighborhoodInclusion
  infer_instance

/-- The neighborhood's actual output in the smooth locus of the same finite model. -/
def tripleTangentNeighborhoodOutput (i : Bool) :
    tripleTangentNeighborhood D data hk a c i ⟶ (U).toScheme :=
  secantBranchNeighborhoodOutput t (j i) (f i) U

/-- The complete neighborhood output contracts to the original ordered tangent formula. -/
@[reassoc] theorem tripleTangentNeighborhoodOutput_contraction (i : Bool) :
    tripleTangentNeighborhoodOutput D data hk a c i ≫ (U).ι ≫
        finiteGlobalContraction hπ data k hk =
      tripleTangentNeighborhoodInclusion D data hk a c i ≫
        dividedTangentToCurve W s (d).b3 (d).b4 (d).b6 a c
          (d).factor3 (d).factor4 (d).factor6 := by
  rw [tripleTangentNeighborhoodOutput, secantBranchNeighborhoodOutput_inclusion_assoc]
  exact tripleTangentBranchOutput_contraction D data hk a c i _ _
    (secantBranchNeighborhood_source t (j i) (f i) U)

/-- Both input functions remain the original ordered input functions on each neighborhood. -/
theorem tripleTangentNeighborhood_input (i : Bool)
    (b : Coordinate W s (d).b3 (d).b4 (d).b6 →ₐ[R] S) :
    secantBranchNeighborhoodBranch t (j i) (f i) U ≫ j i ≫
        Spec.map (CommRingCat.ofHom b.toRingHom) =
      tripleTangentNeighborhoodInclusion D data hk a c i ≫ t ≫
        Spec.map (CommRingCat.ofHom b.toRingHom) :=
  secantBranchNeighborhood_input t (j i) (f i) U _

/-- The neighborhood output retains the coefficient structure of the original tangent. -/
@[reassoc] theorem tripleTangentNeighborhoodOutput_structure (i : Bool) :
    tripleTangentNeighborhoodOutput D data hk a c i ≫ (U).ι ≫ base =
      tripleTangentNeighborhoodInclusion D data hk a c i ≫
        Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  change _ ≫ (U).ι ≫ finiteGlobalContraction hπ data k hk ≫
    WeierstrassIntegralChart.integralCurveStructure W = _
  rw [tripleTangentNeighborhoodOutput_contraction_assoc, dividedTangentToCurve_structure]

end FLT.Mazur.WeierstrassDividedDepth

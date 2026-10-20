/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleNormalizedBranchLift
public import FLT.Mazur.WeierstrassDividedShearTangentScheme

/-!
# The normalized finite-model output contracts to original tangent addition

The constructed normalized branch output agrees with the unsheared tangent
formula on every common scheme domain retaining the original input maps.
No originally smooth output hypothesis is needed for this comparison.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {start n k : ℕ} (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (a c : Coordinate W (π ^ (start + k))
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b3 (data ⟨k, Nat.lt_succ_of_le hk⟩).b4
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b6 →ₐ[R] S)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
local notation "r" => nodalSecondShear D (start + k)
local notation "V" => rootShearCurve W r
local notation "sd" => shearData d r
local notation "a'" => branchShearInput W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 r a
local notation "c'" => branchShearInput W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 r c
local notation "B" => DividedTangentBranchRing V (π ^ (start + k)) (sd).b3 (sd).b4 (sd).b6 a' c'
local notation "T" => DividedTangentRing W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 a c
local notation "T'" => DividedTangentRing V (π ^ (start + k)) (sd).b3 (sd).b4 (sd).b6 a' c'
local notation "res" => dividedTangentBranchRestriction
  V (π ^ (start + k)) (sd).b3 (sd).b4 (sd).b6 a' c'
local notation "hπ" => D.uniformizer_ne_zero

/-- Construct the normalized first output from the original input maps. -/
def tripleBranchOutput : Spec (.of B) ⟶ finiteGlobalModel hπ data k hk :=
  finiteTripleNormalizedBranchLift D data hk a' c'

/-- The constructed output retains the original coefficient point. -/
@[reassoc] theorem tripleBranchOutput_structure :
    tripleBranchOutput D data hk a c ≫ finiteGlobalStructure hπ data k hk =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
  finiteTripleNormalizedBranchLift_structure ..

/-- The normalized output is the original unsheared tangent sum on every common domain. -/
theorem tripleBranchOutput_original_contraction {X : Scheme}
    (p : X ⟶ Spec (.of B)) (q : X ⟶ Spec (.of T))
    (hpq : p ≫ Spec.map (CommRingCat.ofHom (algebraMap S B)) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) :
    p ≫ tripleBranchOutput D data hk a c ≫ finiteGlobalContraction hπ data k hk =
      q ≫ dividedTangentToCurve W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 a c
        (d).factor3 (d).factor4 (d).factor6 := by
  have hres : Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S T')) =
        Spec.map (CommRingCat.ofHom (algebraMap S B)) := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext z
    exact dividedTangentBranchRestriction_source V (π ^ (start + k)) (sd).b3 (sd).b4 (sd).b6 a' c' z
  have hpair : (p ≫ Spec.map (CommRingCat.ofHom (res).toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S T')) =
        q ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)) := by
    rw [Category.assoc, hres, hpq]
  have hout := dividedShearTangent_scheme W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 r a c
    (d).factor3 (d).factor4 (d).factor6 (sd).factor3 (sd).factor4 (sd).factor6
    (p ≫ Spec.map (CommRingCat.ofHom (res).toRingHom)) q hpair
  simpa only [tripleBranchOutput, finiteTripleNormalizedBranchLift_contraction, Category.assoc,
    shearData]
    using hout

variable [IsNoetherianRing R]

/-- The first output is smooth on the entire special fiber of the normalized branch. -/
theorem tripleBranchOutput_smooth (p : PrimeSpectrum B)
    (hp : algebraMap R B π ∈ p.asIdeal) :
    tripleBranchOutput D data hk a c p ∈ (finiteGlobalStructure hπ data k hk).smoothLocus :=
  finiteTripleNormalizedBranchLift_nodal_smooth D data hk a' c' p hp

end FLT.Mazur.WeierstrassDividedDepth

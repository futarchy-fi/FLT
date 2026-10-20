/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteNodalFirstBranchLift
public import FLT.Mazur.WeierstrassDividedNodalSecondNormalization
public import FLT.Mazur.WeierstrassDividedShearGlobalIso
public import FLT.Mazur.WeierstrassDividedShearTangentScheme

/-!
# Actual original branch outputs at arbitrary depths above three input depths

Finite second-coefficient normalization and the proved higher quotients
construct a first branch output for every node depth m ≥ 3h. The output
returns to the original finite model and contracts to the complete original
tangent formula on arbitrary common schemes. At m = 3h it is smooth on
the nodal fiber; larger depths still require further resolution.
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
  {W : WeierstrassCurve R} {π : R} {start n k m : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 3 * (start + k) ≤ m)
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

local notation "dat" => fun i => shearData (data i) r
local notation "g" => finiteNodalFirstBranchLift (nodalSecondShear_depth D (start + k))
  hdepth dat hk (nodalSecondQuotient D (start + k))
  (nodalSecondQuotient_factor D (start + k)) a' c'
local notation "iso" => shearFiniteGlobalIso hπ data r k hk
local notation "cur" => WeierstrassIntegralChart.integralVariableChangeIso W V (⟨1, 0, r, 0⟩)
  (by unfold rootShearCurve; rfl)

/-- Construct the normalized first output from the original input maps. -/
def nodalFirstBranchOutput : Spec (.of B) ⟶ finiteGlobalModel hπ data k hk :=
  g ≫ (iso).hom

/-- The constructed output retains the original coefficient point. -/
@[reassoc] theorem nodalFirstBranchOutput_structure :
    nodalFirstBranchOutput D hdepth data hk a c ≫ finiteGlobalStructure hπ data k hk =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [nodalFirstBranchOutput, Category.assoc, shearFiniteGlobalIso_structure]
  exact finiteNodalFirstBranchLift_structure ..

/-- The normalized branch output is returned through the actual original cubic isomorphism. -/
@[reassoc] theorem nodalFirstBranchOutput_sheared_contraction :
    nodalFirstBranchOutput D hdepth data hk a c ≫ finiteGlobalContraction hπ data k hk =
      Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedTangentToCurve V (π ^ (start + k)) (sd).b3 (sd).b4 (sd).b6 a' c'
          (sd).factor3 (sd).factor4 (sd).factor6 ≫ (cur).hom := by
  rw [nodalFirstBranchOutput, Category.assoc, shearFiniteGlobalIso_contraction,
    finiteNodalFirstBranchLift_contraction_assoc]

/-- The normalized output is the original unsheared tangent sum on every common domain. -/
theorem nodalFirstBranchOutput_original_contraction {X : Scheme}
    (p : X ⟶ Spec (.of B)) (q : X ⟶ Spec (.of T))
    (hpq : p ≫ Spec.map (CommRingCat.ofHom (algebraMap S B)) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) :
    p ≫ nodalFirstBranchOutput D hdepth data hk a c ≫ finiteGlobalContraction hπ data k hk =
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
  simpa only [nodalFirstBranchOutput_sheared_contraction, Category.assoc, shearData]
    using hout

variable [IsNoetherianRing R]

/-- The first output is smooth on the entire special fiber of the normalized branch. -/
theorem nodalFirstBranchOutput_smooth (hterminal : m = 3 * (start + k))
    (p : PrimeSpectrum B)
    (hp : algebraMap R B π ∈ p.asIdeal) :
    nodalFirstBranchOutput D hdepth data hk a c p ∈
      (finiteGlobalStructure hπ data k hk).smoothLocus := by
  have h := Scheme.Hom.preimage_smoothLocus_eq
    (iso).hom (finiteGlobalStructure hπ data k hk)
  simp only [shearFiniteGlobalIso_structure] at h
  apply h.ge
  exact finiteNodalFirstBranchLift_smooth (nodalSecondShear_depth D (start + k))
    hdepth dat hk (nodalSecondQuotient D (start + k))
    (nodalSecondQuotient_factor D (start + k)) a' c' hterminal p hp

end FLT.Mazur.WeierstrassDividedDepth

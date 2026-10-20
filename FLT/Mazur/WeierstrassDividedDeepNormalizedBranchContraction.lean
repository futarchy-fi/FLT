/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteDeepNormalizedBranchInput
public import FLT.Mazur.WeierstrassDividedShearTangentScheme

/-!
# The normalized finite-model output contracts to original tangent addition

The constructed normalized branch output agrees with the unsheared tangent
formula on every common scheme domain retaining the original input maps.
This works at arbitrary node depth in a supplied finite model;
no originally smooth output hypothesis is needed for this comparison.
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
  {W : WeierstrassCurve R} {π : R} {k n m : ℕ} (D : SplitNodeDepth W π m)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : k + k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "r" => nodalSecondShear D k
local notation "V" => rootShearCurve W r
local notation "sd" => shearData d r
local notation "a'" => branchShearInput W (π ^ k) d.b3 d.b4 d.b6 r a
local notation "c'" => branchShearInput W (π ^ k) d.b3 d.b4 d.b6 r c
local notation "B" => DividedTangentBranchRing V (π ^ k) (sd).b3 (sd).b4 (sd).b6 a' c'
local notation "T" => DividedTangentRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "T'" => DividedTangentRing V (π ^ k) (sd).b3 (sd).b4 (sd).b6 a' c'
local notation "res" => dividedTangentBranchRestriction
  V (π ^ k) (sd).b3 (sd).b4 (sd).b6 a' c'
local notation "hπ" => D.uniformizer_ne_zero

/-- The normalized output is the original unsheared tangent sum on every common domain. -/
theorem deepNodalBranchOutput_original_contraction {X : Scheme}
    (p : X ⟶ Spec (.of B)) (q : X ⟶ Spec (.of T))
    (hpq : p ≫ Spec.map (CommRingCat.ofHom (algebraMap S B)) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) :
    p ≫ deepNodalBranchOutput D data hj d a c ≫ finiteGlobalContraction hπ data (k + k) hj =
      q ≫ dividedTangentToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
        d.factor3 d.factor4 d.factor6 := by
  have hres : Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S T')) =
        Spec.map (CommRingCat.ofHom (algebraMap S B)) := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext z
    exact dividedTangentBranchRestriction_source V (π ^ k) (sd).b3 (sd).b4 (sd).b6 a' c' z
  have hpair : (p ≫ Spec.map (CommRingCat.ofHom (res).toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S T')) =
        q ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)) := by
    rw [Category.assoc, hres, hpq]
  have hout := dividedShearTangent_scheme W (π ^ k) d.b3 d.b4 d.b6 r a c
    d.factor3 d.factor4 d.factor6 (sd).factor3 (sd).factor4 (sd).factor6
    (p ≫ Spec.map (CommRingCat.ofHom (res).toRingHom)) q hpair
  simpa only [deepNodalBranchOutput, finiteDeepNormalizedBranchLift_contraction, Category.assoc,
    shearData]
    using hout

end FLT.Mazur.WeierstrassDividedDepth

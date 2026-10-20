/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDeepNodalNegativeBranchOutput
public import FLT.Mazur.WeierstrassDividedNegativeTangentScheme

/-!
# Complementary finite-model outputs retain original tangent addition

On every common domain carrying the original tangent formula, the smooth
complementary output contracts to that exact unsheared formula. No
injectivity of the contraction or originally smooth output is assumed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
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
local notation "r" => nodalSecondShear D k
local notation "a'" => branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6 a
local notation "c'" => branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6 c
local notation "O" => DividedShearBranchOverlap W (π ^ k) d.b3 d.b4 d.b6 r a' c'
local notation "f" => dividedShearBranchOverlapOriginal W (π ^ k) d.b3 d.b4 d.b6 r a' c'
local notation "T" => DividedTangentRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "T'" => DividedTangentRing W (π ^ k) d.b3 d.b4 d.b6 a' c'
local notation "hπ" => D.uniformizer_ne_zero

/-- The complementary actual output contracts to the original tangent sum on common domains. -/
theorem deepNodalNegativeBranchOutput_original_contraction {X : Scheme}
    (p : X ⟶ Spec (.of O)) (q : X ⟶ Spec (.of T))
    (hpq : p ≫ Spec.map (CommRingCat.ofHom (algebraMap S O)) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) :
    p ≫ deepNodalNegativeBranchOutput D data hj d a c ≫
        finiteGlobalContraction hπ data (k + k) hj =
      q ≫ dividedTangentToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
        d.factor3 d.factor4 d.factor6 := by
  have hf : Spec.map (CommRingCat.ofHom (f).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S T')) =
        Spec.map (CommRingCat.ofHom (algebraMap S O)) := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext z
    exact dividedShearBranchOverlapOriginal_source W (π ^ k) d.b3 d.b4 d.b6 r a' c' z
  have hpair : (p ≫ Spec.map (CommRingCat.ofHom (f).toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S T')) =
        q ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)) := by
    rw [Category.assoc, hf, hpq]
  have hout := dividedNegativeTangent_scheme W (π ^ k) d.b3 d.b4 d.b6 a c
    d.factor3 d.factor4 d.factor6
    (p ≫ Spec.map (CommRingCat.ofHom (f).toRingHom)) q hpair
  simpa only [deepNodalNegativeBranchOutput_contraction, Category.assoc] using hout

end FLT.Mazur.WeierstrassDividedDepth

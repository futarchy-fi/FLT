/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalShallowNegativeBranchOutput
public import FLT.Mazur.WeierstrassDividedNegativeTangentSecantScheme
public import FLT.Mazur.WeierstrassDividedTangentReverseSecantScheme

/-!
# Shallow-depth branch outputs contract to the original secant formula

Both strict-branch outputs agree after contraction with the original
secant output on arbitrary common scheme refinements. This includes
nonreduced sources and does not assume injectivity of the contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
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
local notation "σ" => nodalSecondShear D k
local notation "a'" => branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6 a
local notation "c'" => branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6 c
local notation "O" => DividedShearBranchOverlap W (π ^ k) d.b3 d.b4 d.b6 σ a' c'
local notation "f" =>
  dividedShearBranchOverlapOriginal W (π ^ k) d.b3 d.b4 d.b6 σ a' c'
local notation "T" => DividedSecantRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "T'" => DividedTangentRing W (π ^ k) d.b3 d.b4 d.b6 a' c'
local notation "hπ" => D.uniformizer_ne_zero

/-- The complementary output contracts to the original secant on every common domain. -/
theorem nodalShallowNegativeBranchOutput_secant_contraction {X : Scheme}
    (p : X ⟶ Spec (.of O)) (q : X ⟶ Spec (.of T))
    (hpq : p ≫ Spec.map (CommRingCat.ofHom (algebraMap S O)) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) :
    p ≫ nodalShallowNegativeBranchOutput D hdepth hm data hj d a c ≫
        finiteGlobalContraction hπ (start := 0) data (m - 2 * k) hj =
      q ≫ dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
        d.factor3 d.factor4 d.factor6 := by
  have hf : Spec.map (CommRingCat.ofHom (f).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S T')) =
        Spec.map (CommRingCat.ofHom (algebraMap S O)) := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext z
    exact dividedShearBranchOverlapOriginal_source W (π ^ k)
      d.b3 d.b4 d.b6 σ a' c' z
  have hpair : (p ≫ Spec.map (CommRingCat.ofHom (f).toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S T')) =
        q ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)) := by
    rw [Category.assoc, hf, hpq]
  have hout := dividedNegativeTangentSecant_scheme W (π ^ k) d.b3 d.b4 d.b6 a c
    d.factor3 d.factor4 d.factor6
    (p ≫ Spec.map (CommRingCat.ofHom (f).toRingHom)) q hpair
  simpa only [nodalShallowNegativeBranchOutput_contraction, Category.assoc] using hout

local notation "B" =>
  DividedShearBranchOverlap W (π ^ k) d.b3 d.b4 d.b6 σ c a
local notation "g" =>
  dividedShearBranchOverlapOriginal W (π ^ k) d.b3 d.b4 d.b6 σ c a
local notation "T₀" => DividedTangentRing W (π ^ k) d.b3 d.b4 d.b6 c a

/-- The swapped strict-branch output contracts to the original ordered secant sum. -/
theorem nodalShallowSwappedBranchOutput_secant_contraction {X : Scheme}
    (p : X ⟶ Spec (.of B)) (q : X ⟶ Spec (.of T))
    (hpq : p ≫ Spec.map (CommRingCat.ofHom (algebraMap S B)) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) :
    p ≫ nodalShallowBranchCommonOutput D hdepth hm data hj d c a ≫
        finiteGlobalContraction hπ (start := 0) data (m - 2 * k) hj =
      q ≫ dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
        d.factor3 d.factor4 d.factor6 := by
  have hg : Spec.map (CommRingCat.ofHom (g).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S T₀)) =
        Spec.map (CommRingCat.ofHom (algebraMap S B)) := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext z
    exact dividedShearBranchOverlapOriginal_source W (π ^ k)
      d.b3 d.b4 d.b6 σ c a z
  have hout := dividedTangentReverseSecant_scheme W (π ^ k)
    d.b3 d.b4 d.b6 c a d.factor3 d.factor4 d.factor6
    (p ≫ Spec.map (CommRingCat.ofHom (g).toRingHom)) q
    (by rw [Category.assoc, hg, hpq])
  simpa only [nodalShallowBranchCommonOutput_contraction, Category.assoc] using hout

end FLT.Mazur.WeierstrassDividedDepth

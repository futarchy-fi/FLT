/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalDeepAdditionGluing

/-!
# Closed-fiber coverage of the combined deep-node partial addition

The glued domain contains the original source images of all covered secant
points and coincident-abscissa tangent points. The secant assertion retains
its vertical-derivative assumptions; the tangent assertion needs none.
Both coverage statements require m > 4*k and k > 0.
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
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k n m : ℕ} (D : SplitNodeDepth W π m)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : k + k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "T" => DividedTangentRing W s d.b3 d.b4 d.b6 a c
local notation "V" => DividedSecantRing W s d.b3 d.b4 d.b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "v" => Spec.map (CommRingCat.ofHom (algebraMap S V))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data (k + k) hj
local notation "U" => (base).smoothLocus
local notation "Ot" => deepNodalTangentBranchOutputOpen D data hj d a c
local notation "Os" => ⨆ i, nodalDeepSecantLocalOpen D data hj d a c i
local notation "ft" => deepNodalTangentGluedOutput D data hj d a c
local notation "fs" => nodalDeepSecantGluedOutput D data hj d a c

local notation "inc" => nodalDeepAdditionInclusion D data hj d a c
local notation "O" => nodalDeepAdditionOpen D data hj d a c
local notation "dx" => a (x W s d.b3 d.b4 d.b6) - c (x W s d.b3 d.b4 d.b6)

/-- The original-source image of each entire formula domain lies in the glued union. -/
theorem nodalDeepAdditionOpen_image (i : Bool)
    (p : nodalDeepAdditionSource D data hj d a c i) :
    inc i p ∈ O :=
  (le_iSup (fun i : Bool => (inc i).opensRange) i) ⟨p, rfl⟩

/-- Every classified nodal secant maps into the actual common partial-addition domain. -/
theorem nodalDeepAdditionOpen_secant
    (hk : 0 < k) (hm : 4 * k < m) (p : PrimeSpectrum V)
    (hp : algebraMap R V π ∈ p.asIdeal)
    (ha : ((IsScalarTower.toAlgHom R S V).comp a)
      (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hc : ((IsScalarTower.toAlgHom R S V).comp c)
      (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal) : v p ∈ O := by
  have h : p ∈ Os :=
    nodalDeepSecantGluedOutput_covers D data hj d a c hk hm p hp ha hc
  exact nodalDeepAdditionOpen_image D data hj d a c false ⟨p, h⟩

/-- Coincident-abscissa nodal tangent points map into the same domain without input restrictions. -/
theorem nodalDeepAdditionOpen_tangent (hk : 0 < k) (hm : 4 * k < m)
    (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal) (hx : algebraMap S T dx ∈ p.asIdeal) : t p ∈ O := by
  have h : p ∈ Ot :=
    deepNodalTangentBranchOutputOpen_mem D data hj d a c hk hm p hp hx
  exact nodalDeepAdditionOpen_image D data hj d a c true ⟨p, h⟩

/-- Every constructed output is relatively smooth in the constructed depth-2k finite model. -/
theorem nodalDeepAddition_range :
    Set.range (nodalDeepAddition D data hj d a c ≫ (U).ι) ⊆ U := by
  rintro _ ⟨p, rfl⟩
  exact (nodalDeepAddition D data hj d a c p).property

end FLT.Mazur.WeierstrassDividedDepth

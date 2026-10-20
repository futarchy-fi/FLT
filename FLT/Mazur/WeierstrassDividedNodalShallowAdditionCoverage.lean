/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalShallowAdditionGluing

/-!
# Closed-fiber coverage of the combined shallow partial addition

The glued domain contains the original source images of all covered secant
points and coincident-abscissa tangent points. The secant assertion retains
its vertical-derivative assumptions; the tangent assertion needs none.
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
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 2 * k ≤ m) (hm : m ≤ 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : m - 2 * k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "T" => DividedTangentRing W s d.b3 d.b4 d.b6 a c
local notation "V" => DividedSecantRing W s d.b3 d.b4 d.b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "v" => Spec.map (CommRingCat.ofHom (algebraMap S V))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ (start := 0) data (m - 2 * k) hj
local notation "U" => (base).smoothLocus
local notation "Ot" => nodalShallowTangentBranchOutputOpen D hdepth hm data hj d a c
local notation "Os" => ⨆ i, nodalShallowSecantLocalOpen D hdepth hm data hj d a c i
local notation "ft" => nodalShallowTangentGluedOutput D hdepth hm data hj d a c
local notation "fs" => nodalShallowSecantGluedOutput D hdepth hm data hj d a c

local notation "inc" => nodalShallowAdditionInclusion D hdepth hm data hj d a c
local notation "O" => nodalShallowAdditionOpen D hdepth hm data hj d a c
local notation "dx" => a (x W s d.b3 d.b4 d.b6) - c (x W s d.b3 d.b4 d.b6)

/-- The original-source image of each entire formula domain lies in the glued union. -/
theorem nodalShallowAdditionOpen_image (i : Bool)
    (p : nodalShallowAdditionSource D hdepth hm data hj d a c i) :
    inc i p ∈ O :=
  (le_iSup (fun i : Bool => (inc i).opensRange) i) ⟨p, rfl⟩

/-- Every classified nodal secant maps into the actual common partial-addition domain. -/
theorem nodalShallowAdditionOpen_secant
    (hk : 0 < k) (hlo : 2 * k < m) (hhi : m < 3 * k) (p : PrimeSpectrum V)
    (hp : algebraMap R V π ∈ p.asIdeal)
    (ha : ((IsScalarTower.toAlgHom R S V).comp a)
      (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hc : ((IsScalarTower.toAlgHom R S V).comp c)
      (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal) : v p ∈ O := by
  have h : p ∈ Os :=
    nodalShallowSecantGluedOutput_covers D hdepth hm data hj d a c hk hlo hhi p hp ha hc
  exact nodalShallowAdditionOpen_image D hdepth hm data hj d a c false ⟨p, h⟩

/-- Coincident-abscissa nodal tangent points map into the same domain without input restrictions. -/
theorem nodalShallowAdditionOpen_tangent
    (hlo : 2 * k < m) (hhi : m < 3 * k) (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal) (hx : algebraMap S T dx ∈ p.asIdeal) : t p ∈ O := by
  have h : p ∈ Ot :=
    nodalShallowTangentBranchOutputOpen_mem D hdepth hm data hj d a c hlo hhi p hp hx
  exact nodalShallowAdditionOpen_image D hdepth hm data hj d a c true ⟨p, h⟩

/-- Every constructed output is relatively smooth in the independently supplied finite model. -/
theorem nodalShallowAddition_range :
    Set.range (nodalShallowAddition D hdepth hm data hj d a c ≫ (U).ι) ⊆ U := by
  rintro _ ⟨p, rfl⟩
  exact (nodalShallowAddition D hdepth hm data hj d a c p).property

end FLT.Mazur.WeierstrassDividedDepth

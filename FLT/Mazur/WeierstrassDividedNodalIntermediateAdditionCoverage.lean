/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalIntermediateAdditionGluing

/-!
# Closed-fiber coverage of the combined intermediate partial addition

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
  nodalIntermediateBranchCommonOutput nodalIntermediateNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m r : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 3 * k ≤ m) (hrk : r ≤ k) (hrm : r ≤ m - 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : k + r ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "T" => DividedTangentRing W s d.b3 d.b4 d.b6 a c
local notation "V" => DividedSecantRing W s d.b3 d.b4 d.b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "v" => Spec.map (CommRingCat.ofHom (algebraMap S V))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ (start := 0) data (k + r) hj
local notation "U" => (base).smoothLocus
local notation "Ot" => nodalIntermediateTangentBranchOutputOpen D hdepth hrk hrm data hj d a c
local notation "Os" => ⨆ i, nodalIntermediateSecantLocalOpen D hdepth hrk hrm data hj d a c i
local notation "ft" => nodalIntermediateTangentGluedOutput D hdepth hrk hrm data hj d a c
local notation "fs" => nodalIntermediateSecantGluedOutput D hdepth hrk hrm data hj d a c

local notation "inc" => nodalIntermediateAdditionInclusion D hdepth hrk hrm data hj d a c
local notation "O" => nodalIntermediateAdditionOpen D hdepth hrk hrm data hj d a c
local notation "dx" => a (x W s d.b3 d.b4 d.b6) - c (x W s d.b3 d.b4 d.b6)

/-- The original-source image of each entire formula domain lies in the glued union. -/
theorem nodalIntermediateAdditionOpen_image (i : Bool)
    (p : nodalIntermediateAdditionSource D hdepth hrk hrm data hj d a c i) :
    inc i p ∈ O :=
  (le_iSup (fun i : Bool => (inc i).opensRange) i) ⟨p, rfl⟩

/-- Every classified nodal secant maps into the actual common partial-addition domain. -/
theorem nodalIntermediateAdditionOpen_secant
    (hk : 0 < k) (hm : m < 4 * k) (hr : r = m - 3 * k) (p : PrimeSpectrum V)
    (hp : algebraMap R V π ∈ p.asIdeal)
    (ha : ((IsScalarTower.toAlgHom R S V).comp a)
      (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hc : ((IsScalarTower.toAlgHom R S V).comp c)
      (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal) : v p ∈ O := by
  have h : p ∈ Os :=
    nodalIntermediateSecantGluedOutput_covers D hdepth hrk hrm data hj d a c hk hm hr p hp ha hc
  exact nodalIntermediateAdditionOpen_image D hdepth hrk hrm data hj d a c false ⟨p, h⟩

/-- Coincident-abscissa nodal tangent points map into the same domain without input restrictions. -/
theorem nodalIntermediateAdditionOpen_tangent
    (hm : m < 4 * k) (hr : r = m - 3 * k) (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal) (hx : algebraMap S T dx ∈ p.asIdeal) : t p ∈ O := by
  have h : p ∈ Ot :=
    nodalIntermediateTangentBranchOutputOpen_mem D hdepth hrk hrm data hj d a c hm hr p hp hx
  exact nodalIntermediateAdditionOpen_image D hdepth hrk hrm data hj d a c true ⟨p, h⟩

/-- Every constructed output is relatively smooth in the independently supplied finite model. -/
theorem nodalIntermediateAddition_range :
    Set.range (nodalIntermediateAddition D hdepth hrk hrm data hj d a c ≫ (U).ι) ⊆ U := by
  rintro _ ⟨p, rfl⟩
  exact (nodalIntermediateAddition D hdepth hrk hrm data hj d a c p).property

end FLT.Mazur.WeierstrassDividedDepth

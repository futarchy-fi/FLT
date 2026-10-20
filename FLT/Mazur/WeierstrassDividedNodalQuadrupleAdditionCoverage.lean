/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalQuadrupleAdditionGluing

/-!
# Closed-fiber coverage of the combined quadruple-depth partial addition

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
  nodalBranchCommonOutput nodalNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k : ℕ} (D : SplitNodeDepth W π (4 * k))
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "T" => DividedTangentRing W s d.b3 d.b4 d.b6 a c
local notation "V" => DividedSecantRing W s d.b3 d.b4 d.b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "v" => Spec.map (CommRingCat.ofHom (algebraMap S V))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ (splitNodeDoubledFamily D) (k + k) le_rfl
local notation "U" => (base).smoothLocus
local notation "Ot" => nodalTangentBranchOutputOpen D d a c
local notation "Os" => ⨆ i, nodalQuadrupleSecantLocalOpen D d a c i
local notation "ft" => nodalTangentGluedOutput D d a c
local notation "fs" => nodalQuadrupleSecantGluedOutput D d a c

local notation "inc" => nodalQuadrupleAdditionInclusion D d a c
local notation "O" => nodalQuadrupleAdditionOpen D d a c
local notation "dx" => a (x W s d.b3 d.b4 d.b6) - c (x W s d.b3 d.b4 d.b6)

/-- The original-source image of each entire formula domain lies in the glued union. -/
theorem nodalQuadrupleAdditionOpen_image (i : Bool)
    (p : nodalQuadrupleAdditionSource D d a c i) :
    inc i p ∈ O :=
  (le_iSup (fun i : Bool => (inc i).opensRange) i) ⟨p, rfl⟩

/-- Every classified nodal secant maps into the actual common partial-addition domain. -/
theorem nodalQuadrupleAdditionOpen_secant
    (hk : 0 < k) (p : PrimeSpectrum V)
    (hp : algebraMap R V π ∈ p.asIdeal)
    (ha : ((IsScalarTower.toAlgHom R S V).comp a)
      (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hc : ((IsScalarTower.toAlgHom R S V).comp c)
      (verticalDerivative W s d.b3 d.b4 d.b6) ∉ p.asIdeal) : v p ∈ O := by
  have h : p ∈ Os :=
    nodalQuadrupleSecantGluedOutput_covers D d a c hk p hp ha hc
  exact nodalQuadrupleAdditionOpen_image D d a c false ⟨p, h⟩

/-- Coincident-abscissa nodal tangent points map into the same domain without input restrictions. -/
theorem nodalQuadrupleAdditionOpen_tangent
    (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal) (hx : algebraMap S T dx ∈ p.asIdeal) : t p ∈ O := by
  have h : p ∈ Ot :=
    nodalTangentBranchOutputOpen_mem D d a c p hp hx
  exact nodalQuadrupleAdditionOpen_image D d a c true ⟨p, h⟩

/-- Every constructed output is relatively smooth in the constructed depth-2k finite model. -/
theorem nodalQuadrupleAddition_range :
    Set.range (nodalQuadrupleAddition D d a c ≫ (U).ι) ⊆ U := by
  rintro _ ⟨p, rfl⟩
  exact (nodalQuadrupleAddition D d a c p).property

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleAdditionGluing

/-!
# Closed-fiber coverage of the combined exact-triple partial addition

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
  tripleBranchCommonOutput tripleNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {start n k : ℕ}
  (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (a c : Coordinate W (π ^ (start + k))
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b3 (data ⟨k, Nat.lt_succ_of_le hk⟩).b4
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b6 →ₐ[R] S)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
local notation "s" => π ^ (start + k)
local notation "T" => DividedTangentRing W s (d).b3 (d).b4 (d).b6 a c
local notation "V" => DividedSecantRing W s (d).b3 (d).b4 (d).b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "v" => Spec.map (CommRingCat.ofHom (algebraMap S V))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "U" => (base).smoothLocus
local notation "Ot" => tripleTangentBranchOutputOpen D data hk a c
local notation "Os" => ⨆ i, tripleSecantLocalOpen D data hk a c i
local notation "ft" => tripleTangentGluedOutput D data hk a c
local notation "fs" => tripleSecantGluedOutput D data hk a c

local notation "inc" => tripleAdditionInclusion D data hk a c
local notation "O" => tripleAdditionOpen D data hk a c
local notation "dx" => a (x W s (d).b3 (d).b4 (d).b6) - c (x W s (d).b3 (d).b4 (d).b6)

/-- The original-source image of each entire formula domain lies in the glued union. -/
theorem tripleAdditionOpen_image (i : Bool)
    (p : tripleAdditionSource D data hk a c i) :
    inc i p ∈ O :=
  (le_iSup (fun i : Bool => (inc i).opensRange) i) ⟨p, rfl⟩

/-- Every classified nodal secant maps into the actual common partial-addition domain. -/
theorem tripleAdditionOpen_secant
    (p : PrimeSpectrum V)
    (hp : algebraMap R V π ∈ p.asIdeal)
    (ha : ((IsScalarTower.toAlgHom R S V).comp a)
      (verticalDerivative W s (d).b3 (d).b4 (d).b6) ∉ p.asIdeal)
    (hc : ((IsScalarTower.toAlgHom R S V).comp c)
      (verticalDerivative W s (d).b3 (d).b4 (d).b6) ∉ p.asIdeal) : v p ∈ O := by
  have h : p ∈ Os :=
    tripleSecantGluedOutput_covers D data hk a c p hp ha hc
  exact tripleAdditionOpen_image D data hk a c false ⟨p, h⟩

/-- Coincident-abscissa nodal tangent points map into the same domain without input restrictions. -/
theorem tripleAdditionOpen_tangent
    (p : PrimeSpectrum T)
    (hp : algebraMap R T π ∈ p.asIdeal) (hx : algebraMap S T dx ∈ p.asIdeal) : t p ∈ O := by
  have h : p ∈ Ot :=
    tripleTangentBranchOutputOpen_mem D data hk a c p hp hx
  exact tripleAdditionOpen_image D data hk a c true ⟨p, h⟩

/-- Every constructed output is relatively smooth in the independently supplied finite model. -/
theorem tripleAddition_range :
    Set.range (tripleAddition D data hk a c ≫ (U).ι) ⊆ U := by
  rintro _ ⟨p, rfl⟩
  exact (tripleAddition D data hk a c p).property

end FLT.Mazur.WeierstrassDividedDepth

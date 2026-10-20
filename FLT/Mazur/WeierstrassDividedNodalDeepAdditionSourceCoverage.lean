/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalDeepAdditionCoverage

/-!
# Original-source coverage of the deep-node partial addition

Every closed-fiber input point in either formula open is covered when
both input vertical derivatives are nonzero. The coincident-abscissa
tangent case is also covered without either derivative hypothesis.
These coverage results hold for m > 4*k and k > 0.
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

local notation "O" => nodalDeepAdditionOpen D data hj d a c
local notation "dx" => a (x W s d.b3 d.b4 d.b6) - c (x W s d.b3 d.b4 d.b6)
local notation "E" => dividedTangentDenominator W s d.b3 d.b4 d.b6 a c
local notation "δ" => verticalDerivative W s d.b3 d.b4 d.b6

/-- Every original nodal source point in the secant open has the constructed smooth output. -/
theorem nodalDeepAdditionOpen_source_secant
    (hk : 0 < k) (hm : 4 * k < m) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (ha : a δ ∉ p.asIdeal) (hc : c δ ∉ p.asIdeal) (hx : dx ∉ p.asIdeal) : p ∈ O := by
  obtain ⟨q, hq⟩ := (PrimeSpectrum.localization_away_comap_range V dx).ge hx
  have hπq : algebraMap R V π ∈ q.asIdeal := by
    rw [IsScalarTower.algebraMap_apply R S V]
    change algebraMap R S π ∈ (PrimeSpectrum.comap (algebraMap S V) q).asIdeal
    rwa [hq]
  have haq : ((IsScalarTower.toAlgHom R S V).comp a) δ ∉ q.asIdeal := by
    change a δ ∉ (PrimeSpectrum.comap (algebraMap S V) q).asIdeal
    rwa [hq]
  have hcq : ((IsScalarTower.toAlgHom R S V).comp c) δ ∉ q.asIdeal := by
    change c δ ∉ (PrimeSpectrum.comap (algebraMap S V) q).asIdeal
    rwa [hq]
  have h := nodalDeepAdditionOpen_secant
    D data hj d a c hk hm q hπq haq hcq
  change PrimeSpectrum.comap (algebraMap S V) q ∈ O at h
  rwa [hq] at h

/-- The original coincident-abscissa tangent case needs no input vertical derivatives. -/
theorem nodalDeepAdditionOpen_source_tangent (hk : 0 < k) (hm : 4 * k < m)
    (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) (hx : dx ∈ p.asIdeal) (he : E ∉ p.asIdeal) :
    p ∈ O := by
  obtain ⟨q, hq⟩ := (PrimeSpectrum.localization_away_comap_range T E).ge he
  have hπq : algebraMap R T π ∈ q.asIdeal := by
    rw [IsScalarTower.algebraMap_apply R S T]
    change algebraMap R S π ∈ (PrimeSpectrum.comap (algebraMap S T) q).asIdeal
    rwa [hq]
  have hxq : algebraMap S T dx ∈ q.asIdeal := by
    change dx ∈ (PrimeSpectrum.comap (algebraMap S T) q).asIdeal
    rwa [hq]
  have h := nodalDeepAdditionOpen_tangent D data hj d a c hk hm q hπq hxq
  change PrimeSpectrum.comap (algebraMap S T) q ∈ O at h
  rwa [hq] at h

/-- The union covers both original formula opens for nodal points with vertical-smooth inputs. -/
theorem nodalDeepAdditionOpen_source_cover
    (hk : 0 < k) (hm : 4 * k < m) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (ha : a δ ∉ p.asIdeal) (hc : c δ ∉ p.asIdeal)
    (hformula : dx ∉ p.asIdeal ∨ E ∉ p.asIdeal) : p ∈ O := by
  by_cases hx : dx ∈ p.asIdeal
  · exact nodalDeepAdditionOpen_source_tangent D data hj d a c hk hm
      p hp hx (hformula.resolve_left (not_not.mpr hx))
  · exact nodalDeepAdditionOpen_source_secant D data hj d a c hk hm
      p hp ha hc hx

end FLT.Mazur.WeierstrassDividedDepth

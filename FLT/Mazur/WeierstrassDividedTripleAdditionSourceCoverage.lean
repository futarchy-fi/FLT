/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleAdditionCoverage

/-!
# Original-source coverage of the exact-triple partial addition

Every closed-fiber input point in either formula open is covered when
both input vertical derivatives are nonzero. The coincident-abscissa
tangent case is also covered without either derivative hypothesis.
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

local notation "O" => tripleAdditionOpen D data hk a c
local notation "dx" => a (x W s (d).b3 (d).b4 (d).b6) - c (x W s (d).b3 (d).b4 (d).b6)
local notation "E" => dividedTangentDenominator W s (d).b3 (d).b4 (d).b6 a c
local notation "δ" => verticalDerivative W s (d).b3 (d).b4 (d).b6

/-- Every original nodal source point in the secant open has the constructed smooth output. -/
theorem tripleAdditionOpen_source_secant
    (p : PrimeSpectrum S)
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
  have h := tripleAdditionOpen_secant
    D data hk a c q hπq haq hcq
  change PrimeSpectrum.comap (algebraMap S V) q ∈ O at h
  rwa [hq] at h

/-- The original coincident-abscissa tangent case needs no input vertical derivatives. -/
theorem tripleAdditionOpen_source_tangent
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
  have h := tripleAdditionOpen_tangent D data hk a c q hπq hxq
  change PrimeSpectrum.comap (algebraMap S T) q ∈ O at h
  rwa [hq] at h

/-- The union covers both original formula opens for nodal points with vertical-smooth inputs. -/
theorem tripleAdditionOpen_source_cover
    (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (ha : a δ ∉ p.asIdeal) (hc : c δ ∉ p.asIdeal)
    (hformula : dx ∉ p.asIdeal ∨ E ∉ p.asIdeal) : p ∈ O := by
  by_cases hx : dx ∈ p.asIdeal
  · exact tripleAdditionOpen_source_tangent D data hk a c
      p hp hx (hformula.resolve_left (not_not.mpr hx))
  · exact tripleAdditionOpen_source_secant D data hk a c
      p hp ha hc hx

end FLT.Mazur.WeierstrassDividedDepth

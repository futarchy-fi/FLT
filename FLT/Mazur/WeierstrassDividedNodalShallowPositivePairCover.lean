/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalReflectedSecantCoverage
public import FLT.Mazur.WeierstrassDividedNodalShallowTangentNeighborhoodCover

/-!
# Smooth outputs cover positive equal-depth shallow pairs

Combine the normalized reflected secant with the two existing shallow tangent
neighborhoods. Every positive punctured pair has an actual local smooth output,
including coincident abscissae. All three outputs use the same supplied model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsNoetherianRing R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ} (D : SplitNodeDepth W π m)
  (hlo : 2 * k < m) (hhi : m < 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : m - 2 * k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "T" => DividedTangentRing W s d.b3 d.b4 d.b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data (m - 2 * k) hj
local notation "U" => (base).smoothLocus
local notation "hd" => (show m - k - k ≤ n by omega)
local notation "hl" => Nat.le_of_lt hlo
local notation "hm" => (show m ≤ k + 2 * k by omega)
local notation "O" => nodalReflectedDomain D d d (le_refl k) data hd hl hm a c
local notation "N" => nodalShallowTangentNeighborhood D hl (Nat.le_of_lt hhi) data hj d a c
local notation "inc" =>
  nodalShallowTangentNeighborhoodInclusion D hl (Nat.le_of_lt hhi) data hj d a c

/-- One reflected source and two tangent sources in the unchanged pair spectrum. -/
def nodalShallowPositivePairSource : Option Bool → Scheme
  | none => (O).toScheme
  | some b => N b

/-- Each local source retains the complete original pair. -/
def nodalShallowPositivePairInclusion (i : Option Bool) :
    nodalShallowPositivePairSource D hlo hhi data hj d a c i ⟶ Spec (.of S) :=
  match i with
  | none => (O).ι
  | some b => inc b ≫ t

instance nodalShallowPositivePairInclusion_open (i : Option Bool) :
    IsOpenImmersion (nodalShallowPositivePairInclusion D hlo hhi data hj d a c i) := by
  cases i with
  | none => exact inferInstanceAs (IsOpenImmersion (O).ι)
  | some b =>
    change IsOpenImmersion (inc b ≫ t)
    let _ : IsOpenImmersion t := IsOpenImmersion.of_isLocalization
      (dividedTangentDenominator W s d.b3 d.b4 d.b6 a c)
    infer_instance

/-- All three actual outputs land in the same supplied smooth finite model. -/
def nodalShallowPositivePairOutput (i : Option Bool) :
    nodalShallowPositivePairSource D hlo hhi data hj d a c i ⟶ (U).toScheme :=
  match i with
  | none => nodalReflectedResolvedAddition D d d (le_refl k) data hd hl hm a c
      (m - 2 * k) hj (by omega)
  | some b => nodalShallowTangentNeighborhoodOutput D hl (Nat.le_of_lt hhi) data hj d a c b

/-- Every output preserves the original coefficient point. -/
@[reassoc] theorem nodalShallowPositivePairOutput_structure (i : Option Bool) :
    nodalShallowPositivePairOutput D hlo hhi data hj d a c i ≫ (U).ι ≫ base =
      nodalShallowPositivePairInclusion D hlo hhi data hj d a c i ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  cases i with
  | none =>
    exact nodalReflectedResolvedAddition_structure D d d (le_refl k)
      data hd hl hm a c (m - 2 * k) hj (by omega)
  | some b =>
    change nodalShallowTangentNeighborhoodOutput D hl (Nat.le_of_lt hhi) data hj d a c b ≫
      (U).ι ≫ base = (inc b ≫ t) ≫ _
    rw [nodalShallowTangentNeighborhoodOutput_structure]
    simp only [Category.assoc, ← Spec.map_comp]
    rfl

local notation "dx" => a (x W s d.b3 d.b4 d.b6) - c (x W s d.b3 d.b4 d.b6)

/-- The three genuine smooth-output sources cover every positive punctured pair. -/
theorem nodalShallowPositivePair_covers (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (hx : a (x W s d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hu : c (x W s d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hy : a (y W s d.b3 d.b4 d.b6) ∈ p.asIdeal)
    (hv : c (y W s d.b3 d.b4 d.b6) ∈ p.asIdeal) :
    ∃ i : Option Bool, p ∈ Set.range
      (nodalShallowPositivePairInclusion D hlo hhi data hj d a c i) := by
  by_cases hδ : dx ∈ p.asIdeal
  · let K := p.asIdeal.ResidueField
    let ρ : S →ₐ[R] K := IsScalarTower.toAlgHom R S K
    have van (b : R) (hb : b ∈ maximalIdeal R) : algebraMap R K b = 0 := by
      rw [D.maximalIdeal_eq, Ideal.mem_span_singleton] at hb
      obtain ⟨v, hv⟩ := hb
      rw [IsScalarTower.algebraMap_apply R S K]
      apply Ideal.algebraMap_residueField_eq_zero.mpr
      rw [hv, map_mul]
      exact p.asIdeal.mul_mem_right _ hp
    have h3 := van d.b3 (Ideal.pow_le_self (by omega)
      (divided_linear_deep_mem D d (by omega)).1)
    have hu0 : ρ (c (x W s d.b3 d.b4 d.b6)) ≠ 0 :=
      fun h => hu (Ideal.algebraMap_residueField_eq_zero.mp h)
    have hy0 : ρ (a (y W s d.b3 d.b4 d.b6)) = 0 :=
      Ideal.algebraMap_residueField_eq_zero.mpr hy
    have hv0 : ρ (c (y W s d.b3 d.b4 d.b6)) = 0 :=
      Ideal.algebraMap_residueField_eq_zero.mpr hv
    have ht : dividedTangentDenominator W s d.b3 d.b4 d.b6 a c ∉ p.asIdeal := by
      intro ht
      have hz := Ideal.algebraMap_residueField_eq_zero.mpr ht
      change ρ (dividedTangentDenominator W s d.b3 d.b4 d.b6 a c) = 0 at hz
      simp only [dividedTangentDenominator, map_add, map_mul, AlgHom.commutes,
        hy0, hv0, h3, zero_add, add_zero] at hz
      exact mul_ne_zero (D.a₁_unit.map (algebraMap R K)).ne_zero hu0 hz
    obtain ⟨q, hq⟩ := (PrimeSpectrum.localization_away_comap_range T
      (dividedTangentDenominator W s d.b3 d.b4 d.b6 a c)).ge ht
    have hpq : algebraMap R T π ∈ q.asIdeal := by
      rw [IsScalarTower.algebraMap_apply R S T]
      change algebraMap R S π ∈ (PrimeSpectrum.comap (algebraMap S T) q).asIdeal
      rwa [hq]
    rcases nodalShallowTangentNeighborhood_covers D hl (Nat.le_of_lt hhi)
      data hj d a c hlo hhi q hpq with hn | ⟨b, v, hv⟩
    · exact (hn (show algebraMap S T dx ∈ q.asIdeal from by
        change dx ∈ (PrimeSpectrum.comap (algebraMap S T) q).asIdeal
        rwa [hq])).elim
    · refine ⟨some b, v, ?_⟩
      change t ((inc b) v) = p
      exact (congrArg (fun z : PrimeSpectrum T => t z) hv).trans hq
  · have hmem : p ∈ O := nodalReflectedDomain_positive_secant_mem D d d (le_refl k)
      data hd hl hm a c (by omega) hlo p hp
      (by simpa only [Nat.sub_self, pow_zero, map_one, one_mul] using hδ) hx hu hy hv
    exact ⟨none, ⟨p, hmem⟩, rfl⟩

end FLT.Mazur.WeierstrassDividedDepth

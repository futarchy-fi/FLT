/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeSmooth
public import FLT.Mazur.WeierstrassSuccessiveXZeroNodeGeometry

/-!
# Exact smooth coverage of the zero-depth successive residue chart

The two original boundary functions cover the smooth part of the whole first exterior.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

open WeierstrassModificationX

/-- Multiplication by an invertible tangent factor preserves vanishing at a prime. -/
theorem fullNode_mul_unit_mem_iff {F : Type u} [Field F] (a c : F)
    (z : PrimeSpectrum (FullNodeOpen a c)) (x v : FullNodeOpen a c) (hv : IsUnit v) :
    x * v ∈ z.asIdeal ↔ x ∈ z.asIdeal := by
  have hunit : v ∉ z.asIdeal := by
    intro h
    exact z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hv)
  rw [z.isPrime.mul_mem_iff_mem_or_mem, or_iff_left hunit]

/-- The original incidence function vanishes exactly with its full-node parameter. -/
theorem fullNodeInverseT_mem_iff {F : Type u} [Field F] (a c : F) (ha : IsUnit a)
    (z : PrimeSpectrum (FullNodeOpen a c)) :
    fullNodeInverseT a c ∈ z.asIdeal ↔ fullNodeP a c ∈ z.asIdeal := by
  rw [fullNodeInverseT, fullNode_mul_unit_mem_iff a c z _ _ (fullNodeInv_isUnit a c),
    mul_comm, fullNode_mul_unit_mem_iff a c z _ _ (ha.map (algebraMap F _))]

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : k = 0) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "F" => ResidueField R
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 F
local notation "c" => residue R b6
local notation "a" => residue R W.a₁
local notation "t" => tensorCoord W (π ^ k) π b3 b4 b6 F 0
local notation "v" => tensorCoord W (π ^ k) π b3 b4 b6 F 2
local notation "c₁" => zeroFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4
local notation "c₂" => zeroSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4

/-- The first full node retains both original boundary vanishing conditions. -/
theorem zeroFirstNode_boundary_mem (z : Spec (.of (FullNodeOpen a c))) :
    (t ∈ (c₁ z).asIdeal ↔ fullNodeP a c ∈ z.asIdeal) ∧
      (v ∈ (c₁ z).asIdeal ↔ fullNodeQ a c ∈ z.asIdeal) := by
  rw [zeroFirstNodeChart_eq_spec]
  change (zeroFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4 t ∈ z.asIdeal ↔ _) ∧
    (zeroFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4 v ∈ z.asIdeal ↔ _)
  rw [zeroFirstNodeMap_t, zeroFirstNodeMap_u]
  exact ⟨fullNodeInverseT_mem_iff a c (D.a₁_unit.map (residue R)) z,
    fullNode_mul_unit_mem_iff a c z _ _ (fullNodeInverseV_add_isUnit a c)⟩

/-- The second full node retains both original boundary vanishing conditions. -/
theorem zeroSecondNode_boundary_mem (z : Spec (.of (FullNodeOpen (-a) c))) :
    (t ∈ (c₂ z).asIdeal ↔ fullNodeP (-a) c ∈ z.asIdeal) ∧
      (v ∈ (c₂ z).asIdeal ↔ fullNodeQ (-a) c ∈ z.asIdeal) := by
  rw [zeroSecondNodeChart_eq_spec]
  change (zeroSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4 t ∈ z.asIdeal ↔ _) ∧
    (zeroSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4 v ∈ z.asIdeal ↔ _)
  rw [zeroSecondNodeMap_t, zeroSecondNodeMap_u]
  exact ⟨fullNodeInverseT_mem_iff (-a) c ((D.a₁_unit.map (residue R)).neg) z,
    fullNode_mul_unit_mem_iff (-a) c z _ _ (fullNodeInverseV_add_isUnit (-a) c)⟩

variable {X : Scheme.{u}}
  (g : Spec (.of (ScalarExtension W (π ^ k) π b3 b4 b6 (ResidueField R))) ⟶ X)
  [IsOpenImmersion g] (p : X ⟶ Spec (.of (ResidueField R)))
  [LocallyOfFinitePresentation p]
  (hg : g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap (ResidueField R)
    (ScalarExtension W (π ^ k) π b3 b4 b6 (ResidueField R)))))

include D hk0 hk h3 h4 hg in
/-- The complete smooth part of the actual chart is the union of its two boundary opens. -/
theorem zeroResidue_mem_smooth_iff (z : Spec (.of T)) :
    g z ∈ p.smoothLocus ↔ t ∉ z.asIdeal ∨ v ∉ z.asIdeal := by
  rcases zeroNodeCharts_cover D k hk0 hk b3 b4 b6 h3 h4 z with
    ⟨x, rfl⟩ | ⟨x, rfl⟩
  · have hs := PolygonAtlas.mem_smooth_iff (c₁ ≫ g) p x
    have he : (c₁ ≫ g) ≫ p =
        Spec.map (CommRingCat.ofHom (algebraMap F (FullNodeOpen a c))) := by
      rw [Category.assoc, hg, zeroFirstNodeChart_structure]
    simp only [he] at hs
    have hb := zeroFirstNode_boundary_mem D k hk0 hk b3 b4 b6 h3 h4 x
    exact (hs.trans (fullNode_mem_smooth_iff a c x)).trans
      (or_congr (not_congr hb.1) (not_congr hb.2)).symm
  · have hs := PolygonAtlas.mem_smooth_iff (c₂ ≫ g) p x
    have he : (c₂ ≫ g) ≫ p =
        Spec.map (CommRingCat.ofHom (algebraMap F (FullNodeOpen (-a) c))) := by
      rw [Category.assoc, hg, zeroSecondNodeChart_structure]
    simp only [he] at hs
    have hb := zeroSecondNode_boundary_mem D k hk0 hk b3 b4 b6 h3 h4 x
    exact (hs.trans (fullNode_mem_smooth_iff (-a) c x)).trans
      (or_congr (not_congr hb.1) (not_congr hb.2)).symm

end FLT.Mazur.WeierstrassSuccessiveX

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleNodeSmooth
public import FLT.Mazur.WeierstrassSuccessiveXResidueNodeMaps

/-!
# Full smooth coverage of the positive-depth successive residue chart

The two original boundary functions, rather than just the retained horizontal
one, cover exactly the smooth part of any actual ambient open immersion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- The conic incidence function vanishes exactly with its node parameter. -/
theorem middleNodeT_mem_iff {F : Type u} [Field F] (a c : F) (ha : IsUnit a)
    (z : PrimeSpectrum (MiddleNodeOpen c)) :
    middleNodeT a c ∈ z.asIdeal ↔ middleNodeZ c ∈ z.asIdeal := by
  have hunit : middleNodeV a c + algebraMap F (MiddleNodeOpen c) a ∉ z.asIdeal := by
    intro h
    exact z.isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ h (middleNode_v_add_isUnit a c ha))
  rw [← middleNode_parameter_mul, z.isPrime.mul_mem_iff_mem_or_mem, or_iff_left hunit]

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "F" => ResidueField R
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 F
local notation "c" => residue R b6
local notation "t" => tensorCoord W (π ^ k) π b3 b4 b6 F 0
local notation "v" => tensorCoord W (π ^ k) π b3 b4 b6 F 2
local notation "c₁" => residueMiddleFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4
local notation "c₂" => residueMiddleSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4

/-- Both boundary functions retain their vanishing ideals on the first node. -/
theorem residueFirstNode_boundary_mem (z : Spec (.of (MiddleNodeOpen c))) :
    (t ∈ (c₁ z).asIdeal ↔ middleNodeZ c ∈ z.asIdeal) ∧
      (v ∈ (c₁ z).asIdeal ↔ middleNodeU c ∈ z.asIdeal) := by
  rw [residueMiddleFirstNodeChart_eq_spec]
  change (residueFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4 t ∈ z.asIdeal ↔ _) ∧
    (residueFirstNodeMap D k hk0 hk b3 b4 b6 h3 h4 v ∈ z.asIdeal ↔ _)
  rw [residueFirstNodeMap_coord, residueFirstNodeMap_coord]
  exact ⟨middleNodeT_mem_iff _ _ (D.a₁_unit.map (residue R)) z, Iff.rfl⟩

/-- The opposite node retains the same two boundary vanishing ideals. -/
theorem residueSecondNode_boundary_mem (z : Spec (.of (MiddleNodeOpen c))) :
    (t ∈ (c₂ z).asIdeal ↔ middleNodeZ c ∈ z.asIdeal) ∧
      (v ∈ (c₂ z).asIdeal ↔ middleNodeU c ∈ z.asIdeal) := by
  rw [residueMiddleSecondNodeChart_eq_spec]
  change (residueSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4 t ∈ z.asIdeal ↔ _) ∧
    (residueSecondNodeMap D k hk0 hk b3 b4 b6 h3 h4 v ∈ z.asIdeal ↔ _)
  rw [residueSecondNodeMap_coord, residueSecondNodeMap_coord]
  exact ⟨middleNodeT_mem_iff _ _ (D.a₁_unit.map (residue R)) z, Iff.rfl⟩

variable {X : Scheme.{u}}
  (g : Spec (.of (ScalarExtension W (π ^ k) π b3 b4 b6 (ResidueField R))) ⟶ X)
  [IsOpenImmersion g] (p : X ⟶ Spec (.of (ResidueField R)))
  [LocallyOfFinitePresentation p]
  (hg : g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap (ResidueField R)
    (ScalarExtension W (π ^ k) π b3 b4 b6 (ResidueField R)))))

include D hk0 hk h3 h4 hg in
/-- The complete smooth part of the actual chart is the union of its two boundary opens. -/
theorem residueMiddle_mem_smooth_iff (z : Spec (.of T)) :
    g z ∈ p.smoothLocus ↔ t ∉ z.asIdeal ∨ v ∉ z.asIdeal := by
  rcases residueMiddleNodeCharts_cover D k hk0 hk b3 b4 b6 h3 h4 z with
    ⟨x, rfl⟩ | ⟨x, rfl⟩
  · have hs := PolygonAtlas.mem_smooth_iff (c₁ ≫ g) p x
    have he : (c₁ ≫ g) ≫ p =
        Spec.map (CommRingCat.ofHom (algebraMap F (MiddleNodeOpen c))) := by
      rw [Category.assoc, hg, residueMiddleFirstNodeChart_structure]
    simp only [he] at hs
    have hb := residueFirstNode_boundary_mem D k hk0 hk b3 b4 b6 h3 h4 x
    exact (hs.trans (middleNode_mem_smooth_iff c x)).trans
      (or_congr (not_congr hb.1) (not_congr hb.2)).symm
  · have hs := PolygonAtlas.mem_smooth_iff (c₂ ≫ g) p x
    have he : (c₂ ≫ g) ≫ p =
        Spec.map (CommRingCat.ofHom (algebraMap F (MiddleNodeOpen c))) := by
      rw [Category.assoc, hg, residueMiddleSecondNodeChart_structure]
    simp only [he] at hs
    have hb := residueSecondNode_boundary_mem D k hk0 hk b3 b4 b6 h3 h4 x
    exact (hs.trans (middleNode_mem_smooth_iff c x)).trans
      (or_congr (not_congr hb.1) (not_congr hb.2)).symm

end FLT.Mazur.WeierstrassSuccessiveX

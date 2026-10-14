/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationTerminalSections
public import FLT.Mazur.WeierstrassDilatationResidueBoundaryFunctions

/-!
# Actual odd-terminal sections land on punctured node branches

The residue tensor evaluation of every integral section avoids the origin of
its normalized node. The branch cover is applied to the actual spectrum map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
/-- Seal change of coordinates of a section without unfolding the tensor equivalence. -/
irreducible_def normalizedSectionEvaluation {F B N : Type u}
    [CommRing F] [CommRing B] [CommRing N] [Algebra F B] [Algebra F N]
    (f : B →ₐ[F] F) (e : B ≃ₐ[F] N) : N →ₐ[F] F :=
  f.comp e.symm.toAlgHom

/-- The sealed coordinate change recovers the original evaluation. -/
theorem normalizedSectionEvaluation_apply {F B N : Type u}
    [CommRing F] [CommRing B] [CommRing N] [Algebra F B] [Algebra F N]
    (f : B →ₐ[F] F) (e : B ≃ₐ[F] N) (z : B) :
    normalizedSectionEvaluation f e (e z) = f z := by
  rw [normalizedSectionEvaluation_def]
  exact congrArg f (e.symm_apply_apply z)

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ depth) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6) (hp : 2 * k < depth)
local notation "K" => ResidueField R
local notation "C" => Coordinate W (π ^ k) b3 b4 b6
local notation "e" => residuePolygonEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hp
local notation "E" => residueNodeIso D k hk0 hk b3 b4 b6 h3 h4 h6 hp

/-- Residue evaluation on the actual tensor chart of an integral section. -/
def sectionResidueEvaluation (f : C →ₐ[R] R) :
    ScalarExtension W (π ^ k) b3 b4 b6 K →ₐ[K] K :=
  AlgHom.liftEquiv R K C K ((IsScalarTower.toAlgHom R R K).comp f)

omit [IsDomain R] in
@[simp] theorem sectionResidueEvaluation_x (f : C →ₐ[R] R) :
    sectionResidueEvaluation k b3 b4 b6 f (tensorX W (π ^ k) b3 b4 b6 K) =
      residue R (f (x W (π ^ k) b3 b4 b6)) := by
  exact (AlgHom.liftEquiv_tmul _ (1 : K) _).trans (one_smul K _)

omit [IsDomain R] in
@[simp] theorem sectionResidueEvaluation_y (f : C →ₐ[R] R) :
    sectionResidueEvaluation k b3 b4 b6 f (tensorY W (π ^ k) b3 b4 b6 K) =
      residue R (f (y W (π ^ k) b3 b4 b6)) := by
  exact (AlgHom.liftEquiv_tmul _ (1 : K) _).trans (one_smul K _)

/-- The same section evaluated in the ordered polygon-node coordinates. -/
def sectionNodeEvaluation (f : C →ₐ[R] R) :
    PolygonNodeEqualizer.A (R := K) →ₐ[K] K :=
  normalizedSectionEvaluation (sectionResidueEvaluation k b3 b4 b6 f) e

include D hk0 hk h3 h4 h6 hp in
/-- At odd final depth at least one actual normalized branch coordinate is nonzero. -/
theorem sectionNodeEvaluation_avoids_origin (ho : depth = 2 * k + 1)
    (f : C →ₐ[R] R) :
    sectionNodeEvaluation D k hk0 hk b3 b4 b6 h3 h4 h6 hp f
        PolygonNodeLocalization.x ≠ 0 ∨
      sectionNodeEvaluation D k hk0 hk b3 b4 b6 h3 h4 h6 hp f
        PolygonNodeLocalization.y ≠ 0 := by
  let g := sectionNodeEvaluation D k hk0 hk b3 b4 b6 h3 h4 h6 hp f
  have he (z) : g ((e) z) = sectionResidueEvaluation k b3 b4 b6 f z := by
    dsimp only [g]
    exact normalizedSectionEvaluation_apply _ _ _
  by_contra hn
  obtain ⟨hx, hy⟩ := not_or.mp hn
  have hx : g PolygonNodeLocalization.x = 0 := not_not.mp hx
  have hy : g PolygonNodeLocalization.y = 0 := not_not.mp hy
  have hfx := he (tensorX W (π ^ k) b3 b4 b6 K)
  have hfy := he (tensorY W (π ^ k) b3 b4 b6 K)
  rw [residuePolygonEquiv_x, map_mul, map_sub, hx, hy, sub_self, mul_zero,
    sectionResidueEvaluation_x] at hfx
  rw [residuePolygonEquiv_y, hx, sectionResidueEvaluation_y] at hfy
  exact (divided_section_avoids_odd_node D k ho b3 b4 b6 h3 h4 h6 f).elim
    (fun h => h hfx.symm) (fun h => h hfy.symm)

include D hk0 hk h3 h4 h6 hp in
/-- Every point of an odd-terminal integral section lies on an actual punctured branch. -/
theorem sectionNodeEvaluation_mem_branches (ho : depth = 2 * k + 1)
    (f : C →ₐ[R] R) (z : Spec (.of K)) :
    Spec.map (CommRingCat.ofHom
        (sectionNodeEvaluation D k hk0 hk b3 b4 b6 h3 h4 h6 hp f).toRingHom) z ∈
      Set.range (PolygonNodeBranches.left K) ∪ Set.range (PolygonNodeBranches.right K) := by
  rw [PolygonNodeBranches.range_left, PolygonNodeBranches.range_right]
  change _ ∉ z.asIdeal ∨ _ ∉ z.asIdeal
  let _ := z.isPrime
  rw [show z.asIdeal = ⊥ from Ideal.eq_bot_of_prime z.asIdeal]
  exact sectionNodeEvaluation_avoids_origin D k hk0 hk b3 b4 b6 h3 h4 h6 hp ho f

/-- Normalized section coordinates retain the complete tensor specialization map. -/
@[reassoc] theorem sectionNodeEvaluation_inclusion (f : C →ₐ[R] R) :
    Spec.map (CommRingCat.ofHom
        (sectionNodeEvaluation D k hk0 hk b3 b4 b6 h3 h4 h6 hp f).toRingHom) ≫ (E).hom =
      Spec.map (CommRingCat.ofHom (sectionResidueEvaluation k b3 b4 b6 f).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change sectionNodeEvaluation D k hk0 hk b3 b4 b6 h3 h4 h6 hp f ((e) z) = _
  exact normalizedSectionEvaluation_apply _ _ _

end FLT.Mazur.WeierstrassDilatation

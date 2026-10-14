/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationEtaleImageModel
public import FLT.Mazur.SchemeRelationOrbitAtlasKernel
public import FLT.Mazur.SchemeRelationSeedOrbit

/-!
# Effective orbit models on saturated original source opens

Descent replaces the possibly nonmonomorphic orbit atlas by its actual open
image in the original source. Full seed models construct full open-source
quotients; no equality of independent seed coordinates is imposed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationOrbitOpenModel
open SchemeRelationRestriction RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {S Z Q : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (s : Z ⟶ A.left)
  [Etale p.left] [Etale s]
local notation "b" => SchemeRelationEtaleBranchPropagation.branch p.left q.left s
local notation "π" => pullback.snd q.left s

/-- A genuine open of the ORIGINAL parameter scheme, even for nonmonomorphic seeds. -/
def sourceOpen : A.left.Opens := SchemeEtaleImageQuotient.image b

/-- Original point orbits describe exactly the constructed open, without quotient assumptions. -/
theorem mem_sourceOpen (x : A.left) : x ∈ sourceOpen (p := p) (q := q) s ↔
    ∃ z : Z, Related p q x (s z) := SchemeRelationMonicSeedKernel.mem_branch_iff_related s x

include e in
/-- The entire original seed image lies in the open, not only generic points. -/
theorem seed_mem (z : Z) : s z ∈ sourceOpen (p := p) (q := q) s :=
  (mem_sourceOpen s (s z)).mpr ⟨z, related_refl e (s z)⟩

include e in
/-- Every original arrow preserves membership in the complete orbit open. -/
theorem saturated : p.left ⁻¹ᵁ sourceOpen (p := p) (q := q) s =
    q.left ⁻¹ᵁ sourceOpen (p := p) (q := q) s := by
  ext a
  change p.left a ∈ sourceOpen (p := p) (q := q) s ↔
    q.left a ∈ sourceOpen (p := p) (q := q) s
  rw [mem_sourceOpen, mem_sourceOpen]
  have h : Related p q (p.left a) (q.left a) := ⟨a, rfl, rfl⟩
  exact ⟨fun ⟨z, hz⟩ ↦ ⟨z, related_trans e (related_symm e h) hz⟩,
    fun ⟨z, hz⟩ ↦ ⟨z, related_trans e h hz⟩⟩

include e in
/-- Covering seeds construct the whole original source as their orbit open. -/
theorem sourceOpen_eq_top [Surjective s] : sourceOpen (p := p) (q := q) s = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨z, rfl⟩ := s.surjective x
  exact seed_mem e s z

variable (w : Z ⟶ Q)
  (H : IsPullback (fst p.left q.left s) (snd p.left q.left s) w w)
local notation "U" => sourceOpen (p := p) (q := q) s
local notation "i" => Scheme.Opens.ι U
local notation "K" => SchemeRelationOrbitAtlas.model_isPullback e s w H

/-- Construct the model on the actual saturated open of the original source. -/
def projection : (U).toScheme ⟶ Q :=
  SchemeRelationEtaleImageModel.projection e b (π ≫ w) K

/-- The model has the FULL original relation on that open as its kernel. -/
theorem isPullback : IsPullback (fst p.left q.left i) (snd p.left q.left i)
    (projection e s w H) (projection e s w H) :=
  SchemeRelationEtaleImageModel.isPullback e b (π ≫ w) K

/-- Its atlas equation retains both the original orbit arrow and seed-model morphism. -/
@[reassoc]
theorem cover_projection : SchemeEtaleImageQuotient.projection b ≫ projection e s w H =
    π ≫ w := SchemeRelationEtaleImageModel.cover_projection e b (π ≫ w) K

/-- Descent keeps the original family base, without any new ground coordinate. -/
@[reassoc]
theorem projection_ground (a : Q ⟶ S) (ha : w ≫ a = s ≫ A.hom) :
    projection e s w H ≫ a = i ≫ A.hom := by
  apply SchemeRelationEtaleImageModel.projection_ground e b (π ≫ w) K a
  change (π ≫ w) ≫ a = (pullback.fst q.left s ≫ p.left) ≫ A.hom
  rw [Category.assoc, ha, ← Category.assoc, ← pullback.condition]
  simp only [Category.assoc, p.w, q.w]

variable [Etale q.left] [Etale w] [Surjective w]

/-- The constructed open-source model is an actual etale cover of the seed quotient. -/
theorem cover : Etale (projection e s w H) ∧ Surjective (projection e s w H) := by
  let _ := SchemeRelationSplitOrbit.projection_surjective e s
  exact ⟨SchemeRelationEtaleImageModel.projection_etale e b (π ≫ w) K,
    SchemeRelationEtaleImageModel.projection_surjective e b (π ≫ w) K⟩

end FLT.Mazur.SchemeRelationOrbitOpenModel

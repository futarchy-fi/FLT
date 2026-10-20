/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantOpenBoundaryTrace
public import FLT.Mazur.InvariantOpenFiniteRelation
public import FLT.Mazur.FiniteProjectiveAffineNorm

/-!
# Constructed invariant trace multipliers on finite domains

Finite flat geometry supplies the local bases of the entire original relation.
Every resulting trace is an actual lifting multiplier for the unchanged closed
invariant boundary map, without a supplied global basis or constant rank.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.RelativeRelationOrbit
open InvariantOpenRelationDiagram SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} {A D B E : Over S} {p q : D ⟶ A} {r s : E ⟶ B}
  (e : CategoryTheory.EquivalenceRelation p q)
  (W : TopologicalSpace.Opens (Orbit e))
  (es : CategoryTheory.EquivalenceRelation p.left q.left)
  [Flat p.left] [LocallyOfFinitePresentation p.left]
attribute [local irreducible] invariantSheaf invariantMap orbitFunctions
  schemeEquivalence
set_option quotPrecheck false
local notation "U" => (pullOpen e W).val
local notation "p₀" => (fst p U).left
local notation "Ω" => (invariantSheaf e).obj.obj (op W)
variable (hW : IsAffineOpen (pullOpen e W).val)
  (hfin : (pullOpen e W).val ≤ finiteTargetOpen p.left)

/-- Geometry constructs the trace in the exact original invariant ring. -/
@[irreducible] def finiteDomainTrace (es : CategoryTheory.EquivalenceRelation p.left q.left)
    (hW : IsAffineOpen U) (hfin : U ≤ finiteTargetOpen p.left)
    (a : Γ((source U).left, ⊤)) : Ω := by
  let _ : IsAffine (source U).left := hW
  let _ := relation_affine_of_le_finiteTarget p U hfin hW
  let _ := fst_finite_of_le_finiteTarget p U hfin
  let hf := (p₀).finite_appTop
  let hp := fst_projective_of_le_finiteTarget p U hfin hW
  exact openInvariantTrace e W es (FiniteProjectiveAffineNorm.chart p₀ hf hp)
    (FiniteProjectiveAffineNorm.chart_basis p₀ hf hp)
    (FiniteProjectiveAffineNorm.chart_cover p₀ hf hp) a

variable (ec : CategoryTheory.EquivalenceRelation r s)
  (u : B ⟶ A) (v : E ⟶ D) (hp : v ≫ p = r ≫ u) (hq : v ≫ q = s ≫ u)
local notation "m" => invariantMap e ec u.left v.left
  (congrArg Over.Hom.left hp) (congrArg Over.Hom.left hq)
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "V" => (pullOpen ec Wc).val
local notation "r₀" => (fst r V).left
local notation "φ" => (show Ω →+* (invariantSheaf ec).obj.obj (op Wc) from
  ((m).c.app (op W)).hom)

/-- On the entire finite domain, every constructed trace lifts every boundary multiple. -/
theorem finiteDomainTrace_mem_sectionLiftIdeal [IsClosedImmersion u.left]
    (H : IsPullback v.left r.left p.left u.left)
    (t : (invariantSheaf ec).obj.obj (op Wc)) (a : Γ((source U).left, ⊤)) :
    finiteDomainTrace e W es hW hfin a ∈ sectionLiftIdeal φ t := by
  let _ : IsAffine (source U).left := hW
  let _ := relation_affine_of_le_finiteTarget p U hfin hW
  let _ := fst_finite_of_le_finiteTarget p U hfin
  have hV : IsAffineOpen V := by
    rw [invariantMap_sourceOpen_eq e ec u.left v.left
      (congrArg Over.Hom.left hp) (congrArg Over.Hom.left hq) W]
    exact hW.preimage u.left
  let _ : IsAffine (source V).left := hV
  let _ : IsAffineHom r₀ := MorphismProperty.of_isPullback
    (openMap_isPullback e ec u v hp hq W H) (inferInstanceAs (IsAffineHom p₀))
  let _ : IsAffine (relation r V).left := isAffine_of_isAffineHom r₀
  unfold finiteDomainTrace
  exact openInvariantTrace_mem_sectionLiftIdeal e W es _ _ _ ec u v hp hq H hW t a

end FLT.Mazur.RelativeRelationOrbit

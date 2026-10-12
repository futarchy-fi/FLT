/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentOverlapScheme

/-!
# Composition on the actual quadratic Cech triple overlap

Compose pairs sharing their middle coefficient projection. The graph of two
successive coefficient operations composes to their actual composite. For
tangent conjugation this is the identity branch, on the original triple
fiber product rather than on a replacement set of Galois labels.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "q" => nodeTangentCover W
local notation "p₁" => pullback.fst q q
local notation "p₂" => pullback.snd q q
local notation "t₁" => pullback.fst p₂ p₁
local notation "t₂" => pullback.snd p₂ p₁

/-- Compose the first/second and second/third pairs of the actual coefficient triple overlap. -/
def nodeTangentCechCompose : pullback p₂ p₁ ⟶ pullback q q :=
  pullback.lift (t₁ ≫ p₁) (t₂ ≫ p₂) (by
    rw [Category.assoc, pullback.condition (f := q) (g := q), ← Category.assoc,
      pullback.condition (f := p₂) (g := p₁), Category.assoc, pullback.condition (f := q) (g := q),
      Category.assoc])

@[reassoc] theorem nodeTangentCechCompose_fst :
    nodeTangentCechCompose W ≫ p₁ = t₁ ≫ p₁ := pullback.lift_fst _ _ _

@[reassoc] theorem nodeTangentCechCompose_snd :
    nodeTangentCechCompose W ≫ p₂ = t₂ ≫ p₂ := pullback.lift_snd _ _ _

variable (α β : Spec (.of (AdjoinRoot (nodeTangentPolynomial W))) ⟶
  Spec (.of (AdjoinRoot (nodeTangentPolynomial W))))
  (hα : α ≫ nodeTangentCover W = nodeTangentCover W)
  (hβ : β ≫ nodeTangentCover W = nodeTangentCover W)

/-- The graph of an actual coefficient operation in the original Cech scheme. -/
def nodeTangentCechGraph : Spec (.of S) ⟶ pullback q q :=
  pullback.lift (𝟙 _) α (by rw [Category.id_comp, hα])

@[reassoc] theorem nodeTangentCechGraph_fst :
    nodeTangentCechGraph W α hα ≫ p₁ = 𝟙 _ := pullback.lift_fst _ _ _

@[reassoc] theorem nodeTangentCechGraph_snd :
    nodeTangentCechGraph W α hα ≫ p₂ = α := pullback.lift_snd _ _ _

/-- Successive actual coefficient operations determine a point of the original triple overlap. -/
def nodeTangentCechTripleGraph : Spec (.of S) ⟶ pullback p₂ p₁ :=
  pullback.lift (nodeTangentCechGraph W α hα) (α ≫ nodeTangentCechGraph W β hβ) (by
    rw [nodeTangentCechGraph_snd, Category.assoc, nodeTangentCechGraph_fst,
      Category.comp_id])

/-- The Cech composition law keeps the actual composite coefficient operation. -/
theorem nodeTangentCechTripleGraph_compose :
    nodeTangentCechTripleGraph W α β hα hβ ≫ nodeTangentCechCompose W =
      nodeTangentCechGraph W (α ≫ β) (by rw [Category.assoc, hβ, hα]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, nodeTangentCechCompose_fst, nodeTangentCechTripleGraph,
      pullback.lift_fst_assoc, nodeTangentCechGraph_fst]
  · simp only [Category.assoc, nodeTangentCechCompose_snd, nodeTangentCechTripleGraph,
      pullback.lift_snd_assoc, nodeTangentCechGraph_snd]

/-- The identity graph is the original multiplication branch of the tensor overlap. -/
theorem nodeTangentCechGraph_identity :
    nodeTangentCechGraph W (𝟙 _) (Category.id_comp q) = nodeTangentCechIdentity W := by
  apply pullback.hom_ext
  · rw [nodeTangentCechGraph_fst, nodeTangentCechIdentity_fst]
  · rw [nodeTangentCechGraph_snd, nodeTangentCechIdentity_snd]

/-- The conjugation graph is the original twisted multiplication branch. -/
theorem nodeTangentCechGraph_conjugate :
    nodeTangentCechGraph W (nodeTangentCoverConjugation W)
      (nodeTangentCoverConjugation_structure W) = nodeTangentCechConjugate W := by
  apply pullback.hom_ext
  · rw [nodeTangentCechGraph_fst, nodeTangentCechConjugate_fst]
  · rw [nodeTangentCechGraph_snd, nodeTangentCechConjugate_snd]

/-- Two conjugate overlaps compose to the diagonal on the genuine Cech triple scheme. -/
theorem nodeTangentCechConjugate_cocycle :
    nodeTangentCechTripleGraph W (nodeTangentCoverConjugation W)
        (nodeTangentCoverConjugation W) (nodeTangentCoverConjugation_structure W)
        (nodeTangentCoverConjugation_structure W) ≫ nodeTangentCechCompose W =
      nodeTangentCechIdentity W := by
  simp only [nodeTangentCechTripleGraph_compose, nodeTangentCoverConjugation_involutive,
    nodeTangentCechGraph_identity]

end FLT.Mazur

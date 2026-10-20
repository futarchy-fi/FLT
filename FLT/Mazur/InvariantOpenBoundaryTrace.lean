/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineLocallyFreeBoundaryTrace
public import FLT.Mazur.InvariantOpenRelationEquivalence
public import FLT.Mazur.RelativeRelationOpenCartesian

/-!
# Trace lifts in the original orbit-open invariant sheaf

Weighted full-relation traces descend to the unchanged invariant sheaf and
lift boundary multiples on its exact original orbit domain.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.RelativeRelationOrbit
open InvariantOpenRelationDiagram SchemeFunctionGroundChange
open AffineLocallyFreeRelationTrace
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
attribute [local instance] sectionAlgebra
attribute [local irreducible] invariantSheaf invariantMap orbitFunctions
  schemeEquivalence relationTrace source relation fst snd pullOpen
variable {S : Scheme} {A D B E : Over S} {p q : D ⟶ A} {r s : E ⟶ B}
  (e : CategoryTheory.EquivalenceRelation p q)
  (W : TopologicalSpace.Opens (Orbit e))
set_option quotPrecheck false
local notation "U" => (pullOpen e W).val
local notation "p₀" => (fst p U).left
local notation "q₀" => (snd p q U (pullOpen_preimage_eq e W)).left
local notation "Ω" => (invariantSheaf e).obj.obj (op W)
variable [IsAffine (source (pullOpen e W).val).left]
  [IsAffine (relation p (pullOpen e W).val).left]
  (es : CategoryTheory.EquivalenceRelation p.left q.left)
  {ι : Type} (F : ι → (source (pullOpen e W).val).left.affineOpens)
  (hF : ∀ j, AffineOpenNorm.HasBasis (fst p (pullOpen e W).val).left (F j))
  (hcover : ⨆ j, (F j).1 = ⊤)
local notation "er" => schemeEquivalence p q es U (pullOpen_preimage_eq e W)

/-- The full relation trace in the original invariant section ring. -/
@[irreducible] def openInvariantTrace (es : CategoryTheory.EquivalenceRelation p.left q.left)
    {ι : Type} (F : ι → (source U).left.affineOpens)
    (hF : ∀ j, AffineOpenNorm.HasBasis p₀ (F j)) (hcover : ⨆ j, (F j).1 = ⊤)
    (a : Γ((source U).left, ⊤)) : Ω := by
  let t : Γ((source U).left, ⊤) := relationTrace (ι := ι) p₀ q₀ F hF hcover a
  have ht : (p₀).appTop t = (q₀).appTop t :=
    relationTrace_invariant p₀ q₀ F hF hcover
      (schemeEquivalence p q es U (pullOpen_preimage_eq e W)) a
  exact (orbitFunctions e W).symm ⟨t, ht⟩

/-- Its source coordinate is the trace of all original relation arrows. -/
theorem openInvariantTrace_val (a : Γ((source U).left, ⊤)) :
    (orbitFunctions e W (openInvariantTrace (ι := ι) e W es F hF hcover a)).val =
      relationTrace (ι := ι) (D := (relation p U).left) (A := (source U).left)
      p₀ q₀ F hF hcover a :=
  by
    unfold openInvariantTrace
    exact congrArg Subtype.val ((orbitFunctions e W).apply_symm_apply _)

variable (ec : CategoryTheory.EquivalenceRelation r s)
  (u : B ⟶ A) (v : E ⟶ D) (hp : v ≫ p = r ≫ u) (hq : v ≫ q = s ≫ u)
local notation "m" => invariantMap e ec u.left v.left
  (congrArg Over.Hom.left hp) (congrArg Over.Hom.left hq)
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "V" => (pullOpen ec Wc).val
local notation "r₀" => (fst r V).left
local notation "s₀" => (snd r s V (pullOpen_preimage_eq ec Wc)).left
local notation "u₀" => (openSourceMap e ec u v hp hq W).left
local notation "v₀" => (openRelationMap e ec u v hp hq W).left
local notation "φ" => (show Ω →+* (invariantSheaf ec).obj.obj (op Wc) from
  ((m).c.app (op W)).hom)
omit [IsAffine (source (pullOpen e W).val).left]
  [IsAffine (relation p (pullOpen e W).val).left] in
/-- Source coordinates of the exact invariant sheaf map. -/
theorem openTrace_pullback_val (z : Ω) :
    (u₀).appTop (orbitFunctions e W z).val = (orbitFunctions ec Wc (φ z)).val :=
  congrArg Subtype.val (openFunctionMap_natural e ec u v hp hq W z)

variable [IsAffine (source (pullOpen ec ((TopologicalSpace.Opens.map
  (invariantMap e ec u.left v.left (congrArg Over.Hom.left hp)
    (congrArg Over.Hom.left hq)).base).obj W)).val).left]
  [IsAffine (relation r (pullOpen ec ((TopologicalSpace.Opens.map
  (invariantMap e ec u.left v.left (congrArg Over.Hom.left hp)
    (congrArg Over.Hom.left hq)).base).obj W)).val).left]

include es in
/-- Weighted traces lift the original boundary multiple in full source coordinates. -/
theorem openTrace_weighted_source (H : IsPullback v.left r.left p.left u.left)
    (t : (invariantSheaf ec).obj.obj (op Wc))
    (b : Γ((source U).left, ⊤)) (hb : (u₀).appTop b = (orbitFunctions ec Wc t).val)
    (a : Γ((source U).left, ⊤)) :
    (u₀).appTop (relationTrace p₀ q₀ F hF hcover (a * b)) =
      (u₀).appTop (relationTrace p₀ q₀ F hF hcover a) * (orbitFunctions ec Wc t).val := by
  have ht : (r₀).appTop (orbitFunctions ec Wc t).val =
      (s₀).appTop (orbitFunctions ec Wc t).val := (orbitFunctions ec Wc t).property
  have h := boundary_weightedTrace p₀ q₀ F hF hcover
    (schemeEquivalence p q es U (pullOpen_preimage_eq e W)) r₀ s₀ u₀ v₀
    (openMap_isPullback e ec u v hp hq W H)
    (congrArg Over.Hom.left (openMap_snd e ec u v hp hq W))
    ⟨(orbitFunctions ec Wc t).val, ht⟩ b hb a
  exact congrArg Subtype.val h

/-- The weighted lift is an equality in the original invariant boundary sheaf. -/
theorem openInvariantTrace_weighted (H : IsPullback v.left r.left p.left u.left)
    (t : (invariantSheaf ec).obj.obj (op Wc))
    (b : Γ((source U).left, ⊤)) (hb : (u₀).appTop b = (orbitFunctions ec Wc t).val)
    (a : Γ((source U).left, ⊤)) :
    φ (openInvariantTrace e W es F hF hcover (a * b)) =
      φ (openInvariantTrace e W es F hF hcover a) * t := by
  apply (orbitFunctions ec Wc).injective
  rw [map_mul]
  apply Subtype.ext
  change (orbitFunctions ec Wc
    (φ (openInvariantTrace e W es F hF hcover (a * b)))).val =
      (orbitFunctions ec Wc (φ (openInvariantTrace e W es F hF hcover a))).val *
        (orbitFunctions ec Wc t).val
  have h₁ := openTrace_pullback_val e W ec u v hp hq
    (openInvariantTrace e W es F hF hcover (a * b))
  have h₂ := openTrace_pullback_val e W ec u v hp hq
    (openInvariantTrace e W es F hF hcover a)
  have h₃ := congrArg (u₀).appTop (openInvariantTrace_val e W es F hF hcover (a * b))
  have h₄ := congrArg (u₀).appTop (openInvariantTrace_val e W es F hF hcover a)
  exact h₁.symm.trans (h₃.trans
    ((openTrace_weighted_source e W es F hF hcover ec u v hp hq H t b hb a).trans
      (congrArg (fun z ↦ z * (orbitFunctions ec Wc t).val) (h₄.symm.trans h₂))))

/-- Ambient closed restriction constructs a lift for each trace multiplier. -/
theorem openInvariantTrace_mem_sectionLiftIdeal [IsClosedImmersion u.left]
    (H : IsPullback v.left r.left p.left u.left) (hW : IsAffineOpen U)
    (t : (invariantSheaf ec).obj.obj (op Wc)) (a : Γ((source U).left, ⊤)) :
    openInvariantTrace (ι := ι) e W es F hF hcover a ∈ sectionLiftIdeal φ t := by
  obtain ⟨b, hb⟩ := openSourceMap_surjective e ec u v hp hq W hW
    (orbitFunctions ec Wc t).val
  exact ⟨openInvariantTrace (ι := ι) e W es F hF hcover (a * b),
    openInvariantTrace_weighted e W es F hF hcover ec u v hp hq H t b hb a⟩

end FLT.Mazur.RelativeRelationOrbit

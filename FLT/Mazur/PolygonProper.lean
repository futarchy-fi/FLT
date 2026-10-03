/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversallyClosedFiniteCover
public import FLT.Mazur.PolygonSeparated
public import FLT.Mazur.PolygonNormalizationFinite
public import FLT.Mazur.ProjectiveSpaceProper
public import FLT.Mazur.ProjectiveLineStandardComparison
/-!
# Properness of polygon pinching cocones

The finite normalization is surjective. Its finite coproduct of projective
lines is universally closed over the field; separatedness and finite
presentation complete the properness proof.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.PolygonProper
open PolygonPinching
variable (K : Type u) [Field K]
/-- The glued projective line is proper over its coefficient field. -/
instance projectiveLine : IsProper (ProjectiveLine.toBase K) := by
  rw [← ProjectiveLine.standardIso_toBase]
  infer_instance
variable (n : ℕ) [NeZero n] (hn : 0 < n) {C : Over (Spec (.of K))}
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
include h in
/-- Every supplied polygon pinching cocone is proper over the field. -/
theorem proper : IsProper C.hom := by
  let X : Fin n → Scheme.{u} := fun _ ↦ ProjectiveLine.scheme K
  let e : (∐ X) ≅ (components K n).left :=
    asIso (sigmaComparison (Over.forget (Spec (.of K))) (fun _ : Fin n ↦ component K))
  let f : (∐ X) ⟶ C.left := e.hom ≫ p.left
  have hi (i : Fin n) : Sigma.ι X i ≫ f ≫ C.hom = ProjectiveLine.toBase K := by
    have he : Sigma.ι X i ≫ e.hom = (componentι K n i).left :=
      ι_comp_sigmaComparison (Over.forget (Spec (.of K))) (fun _ : Fin n ↦ component K) i
    dsimp only [f]
    rw [← Category.assoc, ← Category.assoc, he]
    exact (componentι K n i ≫ p).w
  have hU (i : Fin n) : UniversallyClosed ((sigmaOpenCover X).f i ≫ (f ≫ C.hom)) := by
    change UniversallyClosed (Sigma.ι X i ≫ f ≫ C.hom)
    rw [hi]
    infer_instance
  have : Finite (sigmaOpenCover X).I₀ := inferInstanceAs (Finite (Fin n))
  have hf : UniversallyClosed (f ≫ C.hom) :=
    UniversallyClosedFiniteCover.universallyClosed _ (sigmaOpenCover X) hU
  have hp : Surjective p.left := ⟨PolygonNormalizationFinite.cocone_normalization_surjective
    K n hn p q h⟩
  have : Surjective f := by dsimp [f]; infer_instance
  have := UniversallyClosed.of_comp_surjective f C.hom
  have := PolygonSeparated.cocone K n hn p q h
  have := polygon_lfp K n hn p q h
  exact ⟨⟩
end FLT.Mazur.PolygonProper

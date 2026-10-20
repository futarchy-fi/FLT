/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UnramifiedFiniteSectionMatching
public import FLT.Mazur.GeometricPointCoverCriterion

/-!
# Geometric marking matches extend to actual affine neighborhoods

For finite families of unramified sections, a relabeling on each geometric
test produces exact local morphism equalities on the original base. Residue
fields locate the neighborhood; open section immersions retain its nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UnramifiedGeometricSectionMatching
variable {X S : Scheme} (p : X ⟶ S)
  [FormallyUnramified p] [LocallyOfFiniteType p]
  {L G : Type*} [Finite L] (s t : L → (S ⟶ X))
  (hs : ∀ a, s a ≫ p = 𝟙 S) (ht : ∀ a, t a ≫ p = 𝟙 S) (r : G → L → L)

include hs ht

/-- Geometric matches of finite unramified families extend to full affine-base matches. -/
theorem exists_affine_relabel
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (q : Spec (.of K) ⟶ S),
      ∃ g, ∀ a, q ≫ s (r g a) = q ≫ t a) (x : S) :
    ∃ (g : G) (U : S.Opens), IsAffineOpen U ∧ x ∈ U ∧
      ∀ a, U.ι ≫ s (r g a) = U.ι ≫ t a := by
  let K := AlgebraicClosure (S.residueField x)
  let q : Spec (.of K) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x) K)) ≫
      S.fromSpecResidueField x
  have hq : q (IsLocalRing.closedPoint K) = x := S.fromSpecResidueField_apply x _
  obtain ⟨g, hg⟩ := h K q
  apply UnramifiedFiniteSectionMatching.exists_affine_relabel p s t hs ht r x
  refine ⟨g, fun a => ?_⟩
  have he := congrArg (fun f => f (IsLocalRing.closedPoint K)) (hg a)
  change s (r g a) (q (IsLocalRing.closedPoint K)) = t a (q (IsLocalRing.closedPoint K)) at he
  rwa [hq] at he

end FLT.Mazur.UnramifiedGeometricSectionMatching

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DisjointSectionPicardGluing
public import FLT.Mazur.SectionCoverGeometricMorphisms
public import FLT.Mazur.AcyclicDegreePicardRepresentation

/-!
# Branch gluing for a geometric class with no original global extension

Independent original translation classes glue on a complete disjoint section
cover. Their geometric acyclicity implies acyclicity for every whole lift
above the specified geometric base map. The input Picard class lives only
on the geometric test, not on the original base or the covered source.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  {E U : Over (Spec (.of R))} (p : E ⟶ U) {ι : Type}
  (a : ι → (U ⟶ E)) [∀ i, IsOpenImmersion (a i).left]
  (ha : ∀ i, a i ≫ p = 𝟙 U)
  (hc : ∀ x : E.left, ∃ i, (a i).left (p.left x) = x)
  (hd : Pairwise (fun i j ↦ Disjoint (Set.range (a i).left) (Set.range (a j).left)))
  {K : Type} [Field K] {t : Spec (.of K) ⟶ Spec (.of R)}
  (b : Over.mk t ⟶ U) (s : (relativeFppfSheaf f).obj.obj (op (Over.mk t)))
  (d : ℕ) (c : ι → (relativeFppfSheaf f).obj.obj (op U))

include ha hc hd in
/-- Branchwise translations assemble for every geometric lift, without extending the input class. -/
theorem exists_disjoint_geometric_translation
    (h : ∀ i, s * (relativeFppfSheaf f).obj.map b.op (c i) ∈
      (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t))) :
    ∃ v : (relativeFppfSheaf f).obj.obj (op E),
      (∀ i, (relativeFppfSheaf f).obj.map (a i).op v = c i) ∧
      ∀ w : Over.mk t ⟶ E, w ≫ p = b →
        s * (relativeFppfSheaf f).obj.map w.op v ∈
          (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)) := by
  obtain ⟨v, hv, _⟩ := disjointSection_existsUnique f p a hc hd c
  refine ⟨v, hv, fun w hw ↦ ?_⟩
  obtain ⟨i, hi⟩ := SectionCoverGeometricMorphisms.exists_sheet p.left
    (fun i ↦ (a i).left) (fun i ↦ congrArg Over.Hom.left (ha i)) hc b.left w.left
      (congrArg Over.Hom.left hw)
  have hw' : w = b ≫ a i := Over.OverMorphism.ext hi
  rw [hw', op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hv]
  exact h i

end FLT.Mazur.CartierAbel

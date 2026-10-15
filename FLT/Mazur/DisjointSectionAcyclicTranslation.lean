/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DisjointSectionPicardGluing
public import FLT.Mazur.AcyclicDegreeSectionCoverDetection

/-!
# One original translation class assembled from disjoint branch translations

Independent translations on a disjoint section cover glue to one original
Picard class. Their fixed-degree divisor conditions hold on the entire
source, hence after every geometric pullback, including all conjugate lifts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f]
  {E U : Over (Spec (.of R))} (p : E ⟶ U) {ι : Type}
  (a : ι → (U ⟶ E)) [∀ i, IsOpenImmersion (a i).left]
  (hc : ∀ x : E.left, ∃ i, (a i).left (p.left x) = x)
  (hd : Pairwise (fun i j ↦ Disjoint (Set.range (a i).left) (Set.range (a j).left)))
  (s : (relativeFppfSheaf f).obj.obj (op E)) (d : ℕ)
  (c : ι → (relativeFppfSheaf f).obj.obj (op U))

include hc hd in
/-- Branch acyclicity constructs one translation valid on the entire original source. -/
theorem exists_disjoint_acyclic_translation
    (h : ∀ i, (relativeFppfSheaf f).obj.map (a i).op s * c i ∈
      (acyclicDegreePicardSubfunctor f d).obj (op U)) :
    ∃ v : (relativeFppfSheaf f).obj.obj (op E),
      (∀ i, (relativeFppfSheaf f).obj.map (a i).op v = c i) ∧
      s * v ∈ (acyclicDegreePicardSubfunctor f d).obj (op E) := by
  obtain ⟨v, hv, _⟩ := disjointSection_existsUnique f p a hc hd c
  refine ⟨v, hv, ?_⟩
  have ha : ∀ i, (relativeFppfSheaf f).obj.map (a i ≫ 𝟙 E).op (s * v) ∈
      (acyclicDegreePicardSubfunctor f d).obj (op U) := by
    intro i
    simpa only [Category.comp_id, map_mul, hv] using h i
  have hm := (acyclicDegree_mem_iff_sectionCover f p a hc (𝟙 E) (s * v) d).mpr ha
  rw [op_id, (relativeFppfSheaf f).obj.map_id] at hm
  exact hm

include hc hd in
/-- The assembled class works on every test lift, not just the supplied branch sections. -/
theorem exists_disjoint_universal_acyclic_translation
    (h : ∀ i, (relativeFppfSheaf f).obj.map (a i).op s * c i ∈
      (acyclicDegreePicardSubfunctor f d).obj (op U)) :
    ∃ v : (relativeFppfSheaf f).obj.obj (op E),
      (∀ i, (relativeFppfSheaf f).obj.map (a i).op v = c i) ∧
      ∀ (T : Over (Spec (.of R))) (b : T ⟶ E),
        (relativeFppfSheaf f).obj.map b.op s * (relativeFppfSheaf f).obj.map b.op v ∈
          (acyclicDegreePicardSubfunctor f d).obj (op T) := by
  obtain ⟨v, hv, hm⟩ := exists_disjoint_acyclic_translation f p a hc hd s d c h
  refine ⟨v, hv, fun T b ↦ ?_⟩
  have ht := (acyclicDegreePicardSubfunctor f d).map b.op hm
  change (relativeFppfSheaf f).obj.map b.op (s * v) ∈
    (acyclicDegreePicardSubfunctor f d).obj (op T) at ht
  simpa only [map_mul] using ht

end FLT.Mazur.CartierAbel

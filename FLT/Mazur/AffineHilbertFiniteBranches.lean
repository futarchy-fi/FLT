/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertRelationNeighborhoods
public import FLT.Mazur.EtaleFiniteBranchNeighborhood

/-!
# Constructed finite etale branches of the full Hilbert relation

Every actual arrow has finite etale branch neighborhoods inside any chosen
original open. Both independent endpoint maps survive, with exactly equal
original Picard classes. These are branches of the full relation, not a
replacement of the relation by a diagonal or a constructed quotient.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "s" => sectionAt f hL d V c k

/-- A finite etale branch through every original arrow, using its actual first endpoint. -/
theorem exists_fst_finite_branch (Ω : (D).left.Opens) (r : (D).left) (hr : r ∈ Ω) :
    ∃ (Z W : Over (Spec (.of R))) (b : W ⟶ A) (t : Z ⟶ W) (a : Z ⟶ D)
      (z : Z.left), IsAffine Z.left ∧ IsAffine W.left ∧ Etale b.left ∧
      Etale t.left ∧ IsFinite t.left ∧ Surjective t.left ∧ Etale a.left ∧
      a ≫ p = t ≫ b ∧ a.left z = r ∧ Set.range a.left ⊆ Ω :=
  EtaleFiniteBranchNeighborhood.exists_cover p Ω r hr

/-- The independent second endpoint also admits finite etale branch neighborhoods. -/
theorem exists_snd_finite_branch (Ω : (D).left.Opens) (r : (D).left) (hr : r ∈ Ω) :
    ∃ (Z W : Over (Spec (.of R))) (b : W ⟶ A) (t : Z ⟶ W) (a : Z ⟶ D)
      (z : Z.left), IsAffine Z.left ∧ IsAffine W.left ∧ Etale b.left ∧
      Etale t.left ∧ IsFinite t.left ∧ Surjective t.left ∧ Etale a.left ∧
      a ≫ q = t ≫ b ∧ a.left z = r ∧ Set.range a.left ⊆ Ω :=
  EtaleFiniteBranchNeighborhood.exists_cover q Ω r hr

omit [Etale V.hom] [IsAffine A.left] [IsOpenImmersion k.left] in
/-- The other branch endpoint has precisely the Picard class from its coefficient base. -/
theorem finite_branch_other_class {Z W : Over (Spec (.of R))}
    (b : W ⟶ A) (t : Z ⟶ W) (a : Z ⟶ D) (h : a ≫ p = t ≫ b) :
    (relativeFppfSheaf f).obj.map (a ≫ q).op s =
      (relativeFppfSheaf f).obj.map t.op ((relativeFppfSheaf f).obj.map b.op s) := by
  have he := congrArg ((relativeFppfSheaf f).obj.map a.op) (equal_class f hL d V c k)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] at he
  rw [← he, h, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

end FLT.Mazur.HilbertChart.AffineRestriction

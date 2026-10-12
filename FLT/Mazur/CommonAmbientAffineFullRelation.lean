/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonAmbientGrassmannianAffineCover

/-!
# Full original relation overlaps between the constructed affine source charts

Two actual pullbacks restrict both endpoints of the original relation to the
constructed affine cover. The resulting overlap retains the original relation
arrow and both independent translation coordinates. Equality of the original
Picard sections gives a unique overlap arrow on every scheme test.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) (V : Over (Spec (.of R)))
  {L : X.Modules} (hL : AmpleLineBundle L)
local notation "C" => commonAmbientGrassmannianAffineCover f d V hL

/-- A constructed affine chart over the unchanged original coefficient ring. -/
def commonAmbientAffineTest (i : (C).I₀) : Over (Spec (.of R)) :=
  Over.mk ((C).f i ≫ (variableHilbertTest f d V).hom)

instance (i : (C).I₀) : IsAffine (commonAmbientAffineTest f d V hL i).left :=
  inferInstanceAs (IsAffine ((C).X i))

/-- Its actual open inclusion in the unrestricted original source. -/
def commonAmbientAffineInclusion (i : (C).I₀) :
    commonAmbientAffineTest f d V hL i ⟶ variableHilbertTest f d V :=
  Over.homMk ((C).f i) rfl

instance (i : (C).I₀) : IsOpenImmersion (commonAmbientAffineInclusion f d V hL i).left :=
  inferInstanceAs (IsOpenImmersion ((C).f i))

variable (c : (relativeFppfSheaf f).obj.obj (op V))
  (i j : (commonAmbientGrassmannianAffineCover f d V hL).I₀)
local notation "a" => commonAmbientAffineInclusion f d V hL i
local notation "b" => commonAmbientAffineInclusion f d V hL j
local notation "p" => variableChartRelationFst f hL d V c
local notation "q" => variableChartRelationSnd f hL d V c

/-- Retain original relation arrows with first endpoint in the first actual affine chart. -/
def commonAmbientAffineRelationFirst : Over (Spec (.of R)) :=
  pullback (variableChartRelationFst f hL d V c)
    (commonAmbientAffineInclusion f d V hL i)

/-- The other endpoint remains in the full unrestricted source. -/
def commonAmbientAffineRelationOther :
    commonAmbientAffineRelationFirst f d V hL c i ⟶ variableHilbertTest f d V :=
  pullback.fst p a ≫ q

/-- The entire original relation between two actual affine charts. -/
def commonAmbientAffineRelation : Over (Spec (.of R)) :=
  pullback (commonAmbientAffineRelationOther f d V hL c i)
    (commonAmbientAffineInclusion f d V hL j)

/-- First original affine endpoint. -/
def commonAmbientAffineRelationFst :
    commonAmbientAffineRelation f d V hL c i j ⟶ commonAmbientAffineTest f d V hL i :=
  pullback.fst _ _ ≫ pullback.snd _ _

/-- Second original affine endpoint. -/
def commonAmbientAffineRelationSnd :
    commonAmbientAffineRelation f d V hL c i j ⟶ commonAmbientAffineTest f d V hL j :=
  pullback.snd _ _

/-- The actual arrow in the original relation is retained. -/
def commonAmbientAffineRelationOriginal :
    commonAmbientAffineRelation f d V hL c i j ⟶ variableChartRelation f hL d V c :=
  pullback.fst _ _ ≫ pullback.fst _ _

/-- First endpoint compatibility with the original full relation. -/
@[reassoc]
theorem commonAmbientAffineRelationOriginal_fst :
    commonAmbientAffineRelationOriginal f d V hL c i j ≫ p =
      commonAmbientAffineRelationFst f d V hL c i j ≫ a := by
  change (pullback.fst _ _ ≫ pullback.fst _ _) ≫ p =
    (pullback.fst _ _ ≫ pullback.snd _ _) ≫ a
  rw [Category.assoc, pullback.condition, ← Category.assoc]

/-- Second endpoint compatibility with the original full relation. -/
@[reassoc]
theorem commonAmbientAffineRelationOriginal_snd :
    commonAmbientAffineRelationOriginal f d V hL c i j ≫ q =
      commonAmbientAffineRelationSnd f d V hL c i j ≫ b := by
  change (pullback.fst _ _ ≫ pullback.fst _ _) ≫ q = pullback.snd _ _ ≫ b
  rw [Category.assoc]
  exact pullback.condition

/-- Both restricted endpoints carry the same original Picard section. -/
theorem commonAmbientAffineRelation_class :
    (relativeFppfSheaf f).obj.map
        (commonAmbientAffineRelationFst f d V hL c i j ≫ a).op
          (variableChartSection f hL d V c) =
      (relativeFppfSheaf f).obj.map
        (commonAmbientAffineRelationSnd f d V hL c i j ≫ b).op
          (variableChartSection f hL d V c) := by
  rw [← commonAmbientAffineRelationOriginal_fst, ← commonAmbientAffineRelationOriginal_snd]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, variableChartRelation_class]

/-- The original endpoint data determine each actual overlap arrow. -/
theorem commonAmbientAffineRelation_hom_ext {T : Over (Spec (.of R))}
    {r s : T ⟶ commonAmbientAffineRelation f d V hL c i j}
    (h₁ : r ≫ commonAmbientAffineRelationFst f d V hL c i j =
      s ≫ commonAmbientAffineRelationFst f d V hL c i j)
    (h₂ : r ≫ commonAmbientAffineRelationSnd f d V hL c i j =
      s ≫ commonAmbientAffineRelationSnd f d V hL c i j) : r = s := by
  have hr : r ≫ commonAmbientAffineRelationOriginal f d V hL c i j =
      s ≫ commonAmbientAffineRelationOriginal f d V hL c i j := by
    apply variableChartRelation_hom_ext f hL d V c
    · simp only [Category.assoc, commonAmbientAffineRelationOriginal_fst]
      exact congrArg (fun k ↦ k ≫ a) h₁
    · simp only [Category.assoc, commonAmbientAffineRelationOriginal_snd]
      exact congrArg (fun k ↦ k ≫ b) h₂
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · exact hr
    · exact h₁
  · exact h₂

/-- Equal original Picard classes give the unique full relation arrow on every scheme test. -/
theorem commonAmbientAffineRelation_lift {T : Over (Spec (.of R))}
    (r : T ⟶ commonAmbientAffineTest f d V hL i)
    (s : T ⟶ commonAmbientAffineTest f d V hL j)
    (h : (relativeFppfSheaf f).obj.map (r ≫ a).op (variableChartSection f hL d V c) =
      (relativeFppfSheaf f).obj.map (s ≫ b).op (variableChartSection f hL d V c)) :
    ∃! t : T ⟶ commonAmbientAffineRelation f d V hL c i j,
      t ≫ commonAmbientAffineRelationFst f d V hL c i j = r ∧
        t ≫ commonAmbientAffineRelationSnd f d V hL c i j = s := by
  obtain ⟨t, ht, _⟩ := variableChartRelation_lift f hL d V c (r ≫ a) (s ≫ b) h
  let t₁ : T ⟶ commonAmbientAffineRelationFirst f d V hL c i := pullback.lift t r ht.1
  have ht₁ : t₁ ≫ commonAmbientAffineRelationOther f d V hL c i = s ≫ b := by
    dsimp only [commonAmbientAffineRelationOther, t₁]
    rw [pullback.lift_fst_assoc, ht.2]
  refine ⟨pullback.lift t₁ s ht₁, ⟨?_, ?_⟩, fun k hk ↦ ?_⟩
  · change pullback.lift t₁ s ht₁ ≫ pullback.fst _ _ ≫ pullback.snd _ _ = r
    rw [pullback.lift_fst_assoc]
    exact pullback.lift_snd _ _ _
  · exact pullback.lift_snd _ _ _
  · apply commonAmbientAffineRelation_hom_ext f d V hL c i j
    · exact hk.1.trans (by
        change r = pullback.lift t₁ s ht₁ ≫ pullback.fst _ _ ≫ pullback.snd _ _
        rw [pullback.lift_fst_assoc]
        exact (pullback.lift_snd _ _ _).symm)
    · exact hk.2.trans (pullback.lift_snd _ _ _).symm

end FLT.Mazur.HilbertChart

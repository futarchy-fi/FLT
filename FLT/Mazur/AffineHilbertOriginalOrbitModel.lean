/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertOriginalOrbitAtlas
public import FLT.Mazur.SchemeRelationOrbitAtlasKernel

/-!
# Effective full seed models in the original proper family

The actual original Picard relation on a complete orbit has the propagated
seed model as its full scheme kernel. Effective etale seed models propagate
without monicity of the seed or equality of its independent coordinates.
Construction of covering effective seed models remains a separate task.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "e" => equivalence f hL d V c k
variable {Z : Scheme} (s : Z ⟶ A.left)
local notation "r" => pullback.fst (Over.Hom.left q) s

local notation "B" => originalOrbitSource f hL d V c k s
local notation "u" => originalOrbitToSource f hL d V c k s
local notation "l" => originalOrbitParameter f hL d V c k s
local notation "p'" => fst f hL d V c l
local notation "q'" => snd f hL d V c l
local notation "π" => pullback.snd (Over.Hom.left q) s

/-- The full original relation comparison retains its first orbit endpoint. -/
@[reassoc]
theorem originalOrbitDoubleIso_fst : (nestedSchemeDoubleIso f hL d V c k u).hom ≫
    SchemeRelationRestriction.fst (p).left (q).left (u).left = (p').left := by
  dsimp only [nestedSchemeDoubleIso, Iso.trans_hom, Functor.mapIso_hom,
    SchemeRelationRestriction.overDoubleIso]
  rw [Category.assoc, SchemeRelationRestriction.overToDouble_fst]
  exact congrArg Over.Hom.left (nestedToFullDouble_fst f hL d V c k u)

/-- The second orbit endpoint remains independent. -/
@[reassoc]
theorem originalOrbitDoubleIso_snd : (nestedSchemeDoubleIso f hL d V c k u).hom ≫
    SchemeRelationRestriction.snd (p).left (q).left (u).left = (q').left := by
  dsimp only [nestedSchemeDoubleIso, Iso.trans_hom, Functor.mapIso_hom,
    SchemeRelationRestriction.overDoubleIso]
  rw [Category.assoc, SchemeRelationRestriction.overToDouble_snd]
  exact congrArg Over.Hom.left (nestedToFullDouble_snd f hL d V c k u)

attribute [local irreducible] SchemeRelationRestriction.doubleDomain
  SchemeRelationRestriction.fst SchemeRelationRestriction.snd

variable {Q : Scheme} (w : Z ⟶ Q)

/-- Propagate the actual seed model over the original orbit source. -/
def originalOrbitModel : (B).left ⟶ Q := π ≫ w

/-- The rebuilt ORIGINAL-family Picard relation is the full propagated seed-model kernel. -/
theorem originalOrbitModel_isPullback
    (H : IsPullback (SchemeRelationRestriction.fst (p).left (q).left s)
      (SchemeRelationRestriction.snd (p).left (q).left s) w w) : IsPullback (p').left (q').left
    (originalOrbitModel f hL d V c k s w) (originalOrbitModel f hL d V c k s w) := by
  apply (SchemeRelationOrbitAtlas.model_isPullback e s w H).of_iso'
    (nestedSchemeDoubleIso f hL d V c k u) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · change (nestedSchemeDoubleIso f hL d V c k u).hom ≫
      SchemeRelationRestriction.fst (p).left (q).left (u).left = (p').left ≫ 𝟙 _
    simpa only [Category.comp_id] using originalOrbitDoubleIso_fst f hL d V c k s
  · change (nestedSchemeDoubleIso f hL d V c k u).hom ≫
      SchemeRelationRestriction.snd (p).left (q).left (u).left = (q').left ≫ 𝟙 _
    simpa only [Category.comp_id] using originalOrbitDoubleIso_snd f hL d V c k s
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl

/-- The original ground coordinate is preserved whenever the seed model preserves it. -/
@[reassoc]
theorem originalOrbitModel_ground (i : Q ⟶ Spec (.of R)) (hi : w ≫ i = s ≫ A.hom) :
    originalOrbitModel f hL d V c k s w ≫ i = (B).hom := by
  change (π ≫ w) ≫ i = (r ≫ (p).left) ≫ A.hom
  calc
    (π ≫ w) ≫ i = (π ≫ s) ≫ A.hom := by simp only [Category.assoc, hi]
    _ = (r ≫ (q).left) ≫ A.hom := by rw [pullback.condition]
    _ = (r ≫ (p).left) ≫ A.hom := by simp only [Category.assoc, (p).w, (q).w]

variable [Etale V.hom] [IsOpenImmersion k.left]

/-- The propagated original-family model is an actual etale cover for an etale seed model. -/
theorem originalOrbitModel_cover [Etale w] [Surjective w] :
    Etale (originalOrbitModel f hL d V c k s w) ∧
      Surjective (originalOrbitModel f hL d V c k s w) :=
  SchemeRelationOrbitAtlas.model_cover e s w

end FLT.Mazur.HilbertChart.AffineRestriction

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonAmbientAffineFullRelation

/-!
# The constructed affine overlaps represent the original presheaf kernel

The actual overlaps are cartesian over the unchanged original Picard sheaf on
all scheme tests. Thus the affine cover preserves the full relation, including
pairs with distinct translation-base coordinates.
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
  (c : (relativeFppfSheaf f).obj.obj (op V))
  (i j : (commonAmbientGrassmannianAffineCover f d V hL).I₀)
local notation "a" => commonAmbientAffineInclusion f d V hL i
local notation "b" => commonAmbientAffineInclusion f d V hL j
local notation "p" => commonAmbientAffineRelationFst f d V hL c i j
local notation "q" => commonAmbientAffineRelationSnd f d V hL c i j

/-- Each actual affine source chart maps to the original Picard presheaf. -/
def commonAmbientAffinePicardMap :
    uliftYoneda.{1}.obj (commonAmbientAffineTest f d V hL i) ⟶
      (relativeFppfSheaf f).obj ⋙ forget CommGrpCat :=
  uliftYoneda.map a ≫ variableHilbertPicardMap f d hL V c

/-- The affine chart map still evaluates the original universal Picard section. -/
theorem commonAmbientAffinePicardMap_apply (T : Over (Spec (.of R)))
    (r : T ⟶ commonAmbientAffineTest f d V hL i) :
    (commonAmbientAffinePicardMap f d V hL c i).app (op T) (ULift.up r) =
      (relativeFppfSheaf f).obj.map (r ≫ a).op (variableChartSection f hL d V c) :=
  (variableChartSection_map f hL d V c (r ≫ a)).symm

/-- The constructed overlap is the entire original presheaf fiber product. -/
theorem commonAmbientAffineRelation_isPullback :
    IsPullback (uliftYoneda.{1}.map p) (uliftYoneda.{1}.map q)
      (commonAmbientAffinePicardMap f d V hL c i)
      (commonAmbientAffinePicardMap f d V hL c j) := by
  apply IsPullback.of_forall_isPullback_app
  intro T
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro r
    change (commonAmbientAffinePicardMap f d V hL c i).app T (ULift.up (r.down ≫ p)) =
      (commonAmbientAffinePicardMap f d V hL c j).app T (ULift.up (r.down ≫ q))
    rw [commonAmbientAffinePicardMap_apply, commonAmbientAffinePicardMap_apply]
    simpa only [Category.assoc, op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using
      congrArg ((relativeFppfSheaf f).obj.map r.down.op)
        (commonAmbientAffineRelation_class f d V hL c i j)
  · intro r s hrs
    apply ULift.ext
    exact commonAmbientAffineRelation_hom_ext f d V hL c i j
      (congrArg ULift.down hrs.1) (congrArg ULift.down hrs.2)
  · intro r s hrs
    change (commonAmbientAffinePicardMap f d V hL c i).app T (ULift.up r.down) =
      (commonAmbientAffinePicardMap f d V hL c j).app T (ULift.up s.down) at hrs
    rw [commonAmbientAffinePicardMap_apply, commonAmbientAffinePicardMap_apply] at hrs
    obtain ⟨t, ht, _⟩ := commonAmbientAffineRelation_lift f d V hL c i j r.down s.down hrs
    exact ⟨ULift.up t, ULift.ext ht.1, ULift.ext ht.2⟩

end FLT.Mazur.HilbertChart

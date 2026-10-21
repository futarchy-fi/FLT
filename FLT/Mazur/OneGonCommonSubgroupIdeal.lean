/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCommonCoefficientSubgroup
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Full ideals of independent one-gon subgroup models

The smooth subgroup comparison induces a Cartesian square of the entire
whole-cubic embeddings. For closed subgroups it identifies the full ideal
sheaves, including nilpotents, through the actual whole-curve isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart WeierstrassDividedDepth CharacterSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A B C G : Type} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A C] [Algebra B C] [AddCommMonoid G]
  (a : A) (b : B) (h : algebraMap A C a = algebraMap B C b)
  (f : (Over.pullback (baseMap A C)).obj (model A G) ⟶
    (originalSmoothBaseChangeGroup C (equation a)).X)
  (g : (Over.pullback (baseMap B C)).obj (model B G) ⟶
    (originalSmoothBaseChangeGroup C (equation b)).X)
  (hs : f ≫ (commonCoefficientSmoothIso a b h).hom =
    (commonGroupIso A B C G).hom ≫ g)
local notation "iA" =>
  CategoryTheory.Functor.map (Over.pullback (baseMap A C)) (smoothCurveInclusion a)
local notation "iB" =>
  CategoryTheory.Functor.map (Over.pullback (baseMap B C)) (smoothCurveInclusion b)

include hs in
/-- The compared smooth subgroup maps give the original full whole-cubic square. -/
theorem commonSubgroup_whole_square :
    (f ≫ iA) ≫ (commonCoefficientCurveIso a b h).hom =
      (commonGroupIso A B C G).hom ≫ (g ≫ iB) := by
  rw [Category.assoc, ← commonCoefficientIso_inclusion, ← Category.assoc, hs,
    Category.assoc]

include hs in
/-- The whole-cubic embedding square is Cartesian on actual schemes. -/
theorem commonSubgroup_whole_isPullback :
    IsPullback (f ≫ iA).left (commonGroupIso A B C G).hom.left
      (commonCoefficientCurveIso a b h).hom.left (g ≫ iB).left := by
  apply IsPullback.of_vert_isIso
  exact ⟨congrArg (fun k => k.left) (commonSubgroup_whole_square a b h f g hs)⟩

include hs in
/-- Closed subgroup comparison retains the entire ideal sheaf, not just its support. -/
theorem commonSubgroup_whole_ideal [IsClosedImmersion (g ≫ iB).left] :
    (f ≫ iA).left.ker =
      (g ≫ iB).left.ker.comap (commonCoefficientCurveIso a b h).hom.left := by
  let q := commonSubgroup_whole_isPullback a b h f g hs
  rw [← q.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  exact Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _

include hs in
/-- Every further test preserves the full ideal comparison. -/
theorem commonSubgroup_whole_ideal_baseChange [IsClosedImmersion (g ≫ iB).left]
    {T : Scheme} (v : T ⟶ ((Over.pullback (baseMap A C)).obj (family a)).left) :
    (f ≫ iA).left.ker.comap v =
      (g ≫ iB).left.ker.comap (v ≫ (commonCoefficientCurveIso a b h).hom.left) := by
  rw [commonSubgroup_whole_ideal a b h f g hs, Scheme.IdealSheafData.comap_comp]

end FLT.Mazur.OneGonSmoothing

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineOverlapTestRecovery
public import FLT.Mazur.SchemeAffineTestComparison
/-!
# Geometric normalization of glued overlap comparisons

Every affine pullback of the glued geometric overlap map normalizes to the effective
comparison in the actual affine-test coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem transport_geometric {W O S T : Scheme.{u}}
    (c : W ⟶ O) (p : O ⟶ S) (q : O ⟶ T) (i : W ⟶ S) (j : W ⟶ T)
    (hi : i = c ≫ p) (hj : j = c ≫ q) (M : S.Modules) (N : T.Modules)
    (a : (pullback i).obj M ⟶ (pullback j).obj N) :
    SheafPullbackLocalComparison.transport c p q i j hi.symm hj.symm M N a ≫
        (pullbackComp c q).hom.app N =
      (pullbackComp c p).hom.app M ≫
        (pullbackCongr hi).inv.app M ≫ a ≫ (pullbackCongr hj).hom.app N := by
  subst i j
  simp only [SheafPullbackLocalComparison.transport, SheafPullbackPathComparison.comparison,
    pullbackCongr, eqToIso_refl, Iso.trans_refl, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp]

variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
attribute [local irreducible] CrossRefinement.effectiveComparison sheaf

/-- The geometric projection paths of an affine overlap test agree over the base. -/
theorem affineOverlapTest_over {A : CommRingCat.{u}} (f : Spec A ⟶ C.baseOverlap C') :
    (f ≫ Limits.pullback.fst C.base C'.base) ≫ C.base =
      (f ≫ Limits.pullback.snd C.base C'.base) ≫ C'.base := by
  rw [Category.assoc, Category.assoc, Limits.pullback.condition]

/-- Normalize the local overlap map into the geometric coordinates of its affine test. -/
theorem overlapChartLocalComparison_normalize
    {A : CommRingCat.{u}} (f : Spec A ⟶ C.baseOverlap C') :
    C.overlapChartLocalComparison C' D f ≫
        (pullbackComp f (Limits.pullback.snd C.base C'.base)).hom.app (C'.sheaf D) =
      (pullbackComp f (Limits.pullback.fst C.base C'.base)).hom.app (C.sheaf D) ≫
        (C.affineTestComparison C' (f ≫ Limits.pullback.fst C.base C'.base)
          (f ≫ Limits.pullback.snd C.base C'.base) (C.affineOverlapTest_over C' f) D).hom := by
  unfold overlapChartLocalComparison affineTestComparison
  exact transport_geometric f (Limits.pullback.fst C.base C'.base)
    (Limits.pullback.snd C.base C'.base) _ _ (Spec.map_preimage _) (Spec.map_preimage _)
    (C.sheaf D) (C'.sheaf D) _

/-- Every affine pullback of the glued map is its geometric effective comparison. -/
theorem baseOverlapComparison_normalize
    {A : CommRingCat.{u}} (f : Spec A ⟶ C.baseOverlap C') :
    (pullback f).map (C.baseOverlapComparison C' D).hom ≫
        (pullbackComp f (Limits.pullback.snd C.base C'.base)).hom.app (C'.sheaf D) =
      (pullbackComp f (Limits.pullback.fst C.base C'.base)).hom.app (C.sheaf D) ≫
        (C.affineTestComparison C' (f ≫ Limits.pullback.fst C.base C'.base)
          (f ≫ Limits.pullback.snd C.base C'.base) (C.affineOverlapTest_over C' f) D).hom := by
  rw [baseOverlapComparison_test]
  exact C.overlapChartLocalComparison_normalize C' D f

end FLT.Mazur.SchemeAffineDescent.Chart

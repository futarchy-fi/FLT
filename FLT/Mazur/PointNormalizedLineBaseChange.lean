/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointNormalizedLineBundle
public import FLT.Mazur.ModuleSheafDualPullbackRestrict

/-!
# Point normalization under compatible change of family

The actual normalized line commutes with pullback along every commuting
pointed family square. Tensor and dual pullback comparisons construct the
sheaf isomorphism, without a flatness hypothesis on either morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.SchemePicard
open FCurve
attribute [local irreducible] ModuleSheafTensor.tensor
variable {X Y S T : Scheme.{u}} (f : X ⟶ S) (e : S ⟶ X)
  (q : Y ⟶ T) (d : T ⟶ Y) (r : Y ⟶ X) (k : T ⟶ S)
  (hf : r ≫ f = q ≫ k) (he : d ≫ r = k ≫ e)
  (L : X.Modules) (hL : LocallyFreeRankOne L)

/-- Point normalization has an actual sheaf comparison for every compatible family square. -/
@[irreducible] def pointNormalizedLineBaseChangeIso :
    (Scheme.Modules.pullback r).obj (pointNormalizedLine f e L) ≅
      pointNormalizedLine q d ((Scheme.Modules.pullback r).obj L) := by
  let N := (Scheme.Modules.pullback e).obj L
  let a : (Scheme.Modules.pullback d).obj ((Scheme.Modules.pullback r).obj L) ≅
      (Scheme.Modules.pullback k).obj N :=
    (Scheme.Modules.pullbackComp d r).app L ≪≫
      (Scheme.Modules.pullbackCongr he).app L ≪≫
        ((Scheme.Modules.pullbackComp k e).app L).symm
  let b : (Scheme.Modules.pullback r).obj
      ((Scheme.Modules.pullback f).obj (moduleSheafDual N)) ≅
      (Scheme.Modules.pullback q).obj
        (moduleSheafDual ((Scheme.Modules.pullback d).obj
          ((Scheme.Modules.pullback r).obj L))) :=
    (Scheme.Modules.pullbackComp r f).app _ ≪≫
      (Scheme.Modules.pullbackCongr hf).app _ ≪≫
        ((Scheme.Modules.pullbackComp q k).app _).symm ≪≫
          (Scheme.Modules.pullback q).mapIso
            (moduleSheafDualPullbackIso k (hL.pullback e) ≪≫ moduleSheafDualIso _ a)
  unfold pointNormalizedLine
  exact ModuleLineBundleTensorPullback.tensorIso r L _ ≪≫
    ModuleSheafTensor.congr (Iso.refl _) b

include hf he in
/-- The sheaf comparison identifies normalization with the original Picard pullback. -/
theorem pointNormalizedLine_baseChange_class :
    pullback r (normalize f e (mk L hL)) =
      normalize q d (pullback r (mk L hL)) := by
  rw [← pointNormalizedLine_class f e L hL, pullback_mk, pullback_mk,
    ← pointNormalizedLine_class q d _ (hL.pullback r)]
  exact mk_eq_of_iso _ _ (pointNormalizedLineBaseChangeIso f e q d r k hf he L hL)

end FLT.Mazur.SchemePicard

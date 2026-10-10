/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalFamilyTwistComparison
public import FLT.Mazur.TensorPullbackIdentity

/-!
# Identity comparison for original twisted sections

The prescribed pullback identity on the original base line preserves the
original section after its direct geometric pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve ModuleSheafTensor SheafPullbackPathComparison
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor ModuleLineBundleTensorPullback.tensorIso
variable {P X T : Scheme.{0}} (p : P ⟶ X) (q : P ⟶ T)
  (L : X.Modules) (B : SchemePicard.LineBundle T)

/-- The identity square comparison is the identity pullback on the original sheaf. -/
@[reassoc]
lemma originalFamilyIdentity_square (N : T.Modules) :
    (comparison (𝟙 P) q (q ≫ 𝟙 T) (by simp)).hom.app N ≫
      (pullbackComp q (𝟙 T)).inv.app N ≫
      (pullback q).map ((pullbackId T).hom.app N) =
        (pullbackId P).hom.app ((pullback q).obj N) := by
  rw [← comparison_comp_id]
  simp only [comparison, Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc]
  change (pullbackComp (𝟙 P) q).hom.app N ≫
    ((pullbackCongr (by simp : 𝟙 P ≫ q = q ≫ 𝟙 T)).hom.app N ≫
      (pullbackCongr (Category.comp_id q)).hom.app N) = _
  simp only [pullbackCongr, eqToIso.hom]
  exact comparison_id_comp q N

/-- The original twist comparison commutes with the prescribed base identity. -/
@[reassoc]
lemma originalFamilyTwistIso_id :
    (originalFamilyTwistIso (𝟙 T) (𝟙 P) (Category.id_comp p)
      (by simp : 𝟙 P ≫ q = q ≫ 𝟙 T) L B).hom ≫
      map (𝟙 ((pullback p).obj L))
        ((pullback q).map ((pullbackId T).hom.app B.val)) =
      (pullbackId P).hom.app (twist q ((pullback p).obj L) B) := by
  dsimp only [originalFamilyTwistIso, Iso.trans_hom, ModuleSheafTensor.congr, Iso.symm_hom]
  erw [Category.assoc, ← map_comp]
  simp only [Category.comp_id, Iso.app, Category.assoc,
    originalFamilyIdentity_square, comparison_id_comp]
  exact ModuleLineBundleTensorPullback.tensorIso_id ((pullback p).obj L)
    ((pullback q).obj B.val)

/-- The direct identity pullback recovers the section by the actual base identity. -/
lemma originalFamilyPullSection_id (s : Γ(twist q ((pullback p).obj L) B, ⊤)) :
    (map (𝟙 ((pullback p).obj L))
      ((pullback q).map ((pullbackId T).hom.app B.val))).app ⊤
      (originalFamilyPullSection (𝟙 T) (𝟙 P) (Category.id_comp p)
        (by simp : 𝟙 P ≫ q = q ≫ 𝟙 T) L B s) = s := by
  change ((originalFamilyTwistIso (𝟙 T) (𝟙 P) (Category.id_comp p)
    (by simp : 𝟙 P ≫ q = q ≫ 𝟙 T) L B).hom ≫
    map (𝟙 ((pullback p).obj L))
      ((pullback q).map ((pullbackId T).hom.app B.val))).app ⊤
      (pullGlobal (𝟙 P) _ s) = s
  rw [originalFamilyTwistIso_id]
  exact ModuleLineBundleTensorPullback.pullbackId_unit_open _ ⊤ s

end FLT.Mazur.CartierAbel

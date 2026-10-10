/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalFamilyTwistComparison
public import FLT.Mazur.OriginalFamilySquareComposition
public import FLT.Mazur.TensorPullbackComposition

/-!
# Composition of the original tensor twist comparisons

Direct pullback of the actual original twisted line commutes with the
prescribed composition maps on both the total space and the base line.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve ModuleSheafTensor SheafPullbackPathComparison
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor tensorIso
variable {P Q R X T U V : Scheme.{0}}
  {p : P ⟶ X} {p' : Q ⟶ X} {p'' : R ⟶ X}
  {q : P ⟶ T} {q' : Q ⟶ U} {q'' : R ⟶ V}
  (k : U ⟶ T) (l : V ⟶ U) (r : Q ⟶ P) (s : R ⟶ Q)
  (hp : r ≫ p = p') (hq : r ≫ q = q' ≫ k)
  (hp' : s ≫ p' = p'') (hq' : s ≫ q' = q'' ≫ l)
  (hp'' : (s ≫ r) ≫ p = p'') (hq'' : (s ≫ r) ≫ q = q'' ≫ (l ≫ k))
  (L : X.Modules) (B : SchemePicard.LineBundle T)

/-- The prescribed total and base composition maps preserve the original twist comparison. -/
@[reassoc]
lemma originalFamilyTwistIso_comp :
    (pullback s).map (originalFamilyTwistIso k r hp hq L B).hom ≫
      (originalFamilyTwistIso l s hp' hq' L (pulledBaseLine k B)).hom ≫
      map (𝟙 ((pullback p'').obj L))
        ((pullback q'').map ((pullbackComp l k).hom.app B.val)) =
    (pullbackComp s r).hom.app (twist q ((pullback p).obj L) B) ≫
      (originalFamilyTwistIso (l ≫ k) (s ≫ r) hp'' hq'' L B).hom := by
  have ha := comparison_assoc s r p (s ≫ r) p' p'' rfl hp hp' hp'' L
  have hc : comparison s r (s ≫ r) rfl = pullbackComp s r := by
    simp [comparison, pullbackCongr]
  rw [hc] at ha
  have hb := original_square_comp q q' q'' k l r s hq hq' hq'' B.val
  simp only [Category.assoc] at hb
  dsimp only [originalFamilyTwistIso, Iso.trans_hom, ModuleSheafTensor.congr,
    Iso.symm_hom, Iso.app, pulledBaseLine]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% tensorIso_naturality]
  rw [← map_comp, ← map_comp]
  simp only [Category.comp_id, Category.assoc]
  rw [ha, hb]
  rw [map_comp]
  rw [tensorIso_comp_assoc]
  rfl

end FLT.Mazur.CartierAbel

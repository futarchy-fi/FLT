/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalFamilyTwistComposition

/-!
# Composition of direct original section pullbacks

The prescribed base-line composition carries the iterated actual section
to its direct composite pullback, without using an orbit representative.
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

/-- The prescribed base composition carries two direct original section pullbacks. -/
lemma originalFamilyPullSection_comp
    (t : Γ(twist q ((pullback p).obj L) B, ⊤)) :
    (map (𝟙 ((pullback p'').obj L))
      ((pullback q'').map ((pullbackComp l k).hom.app B.val))).app ⊤
      (originalFamilyPullSection l s hp' hq' L (pulledBaseLine k B)
        (originalFamilyPullSection k r hp hq L B t)) =
    originalFamilyPullSection (l ≫ k) (s ≫ r) hp'' hq'' L B t := by
  unfold originalFamilyPullSection
  rw [← pullGlobal_naturality]
  change ((pullback s).map (originalFamilyTwistIso k r hp hq L B).hom ≫
    (originalFamilyTwistIso l s hp' hq' L (pulledBaseLine k B)).hom ≫
      map (𝟙 ((pullback p'').obj L))
        ((pullback q'').map ((pullbackComp l k).hom.app B.val))).app ⊤
    (pullGlobal s _ (pullGlobal r _ t)) = _
  rw [originalFamilyTwistIso_comp k l r s hp hq hp' hq' hp'' hq'' L B]
  change (originalFamilyTwistIso (l ≫ k) (s ≫ r) hp'' hq'' L B).hom.app ⊤
    (((pullbackComp s r).hom.app _).app ⊤ (pullGlobal s _ (pullGlobal r _ t))) = _
  rw [pullGlobal_comp_hom]

end FLT.Mazur.CartierAbel

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierAbelTwistBaseChange
public import FLT.Mazur.CartierIdealPullbackComparison
public import FLT.Mazur.SheafPullbackPathComparison

/-!
# Actual twisting-line comparison on original families

Both the fixed line and the original base twist are transported through their
specified scheme-map equalities. No section or representative is reconstructed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve ModuleSheafTensor SheafPullbackPathComparison
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor
variable {P Q X T U : Scheme.{0}} {p : P ⟶ X} {q : P ⟶ T}
  {p' : Q ⟶ X} {q' : Q ⟶ U}
  (k : U ⟶ T) (r : Q ⟶ P) (hp : r ≫ p = p') (hq : r ≫ q = q' ≫ k)
  (L : X.Modules) (B : SchemePicard.LineBundle T)

/-- Pull the original twisted line through the two actual commuting triangles. -/
def originalFamilyTwistIso :
    (pullback r).obj (twist q ((pullback p).obj L) B) ≅
      twist q' ((pullback p').obj L) (pulledBaseLine k B) :=
  ModuleLineBundleTensorPullback.tensorIso r _ _ ≪≫
    congr ((comparison r p p' hp).app L)
      ((comparison r q (q' ≫ k) hq).app B.val ≪≫
        ((pullbackComp q' k).app B.val).symm)

/-- Pull the actual original tensor section through its explicit sheaf comparison. -/
def originalFamilyPullSection (s : Γ(twist q ((pullback p).obj L) B, ⊤)) :
    Γ(twist q' ((pullback p').obj L) (pulledBaseLine k B), ⊤) :=
  (originalFamilyTwistIso k r hp hq L B).hom.app ⊤
    (pullGlobal r (twist q ((pullback p).obj L) B) s)

/-- Regularity survives the original comparison whenever the pulled ideal is Cartier. -/
lemma originalFamilyPullSection_regular (hL : LocallyFreeRankOne L)
    (s : Γ(twist q ((pullback p).obj L) B, ⊤))
    [Mono (globalSectionHom (twist q ((pullback p).obj L) B) s)]
    (hD : EffectiveCartier
      ((lineSectionZeroIdeal (twist_rankOne q _ (hL.pullback p) B) s).comap r)) :
    Mono (globalSectionHom _ (originalFamilyPullSection k r hp hq L B s)) := by
  let _ := idealModulePullbackHom_isIso_of_cartier r
    (lineSectionZeroIdeal_effectiveCartier (twist_rankOne q _ (hL.pullback p) B) s) hD
  let _ := pullGlobal_regular_of_zeroIdeal r (twist_rankOne q _ (hL.pullback p) B) s hD
  unfold originalFamilyPullSection
  rw [← globalSectionHom_naturality]
  infer_instance

/-- The direct pulled section retains the full pulled zero ideal. -/
lemma originalFamilyPullSection_zero (hL : LocallyFreeRankOne L)
    (s : Γ(twist q ((pullback p).obj L) B, ⊤))
    [Mono (globalSectionHom (twist q ((pullback p).obj L) B) s)]
    (hD : EffectiveCartier
      ((lineSectionZeroIdeal (twist_rankOne q _ (hL.pullback p) B) s).comap r)) :
    lineSectionZeroIdeal (twist_rankOne q' _ (hL.pullback p') (pulledBaseLine k B))
        (originalFamilyPullSection k r hp hq L B s) =
      (lineSectionZeroIdeal (twist_rankOne q _ (hL.pullback p) B) s).comap r := by
  let _ := idealModulePullbackHom_isIso_of_cartier r
    (lineSectionZeroIdeal_effectiveCartier (twist_rankOne q _ (hL.pullback p) B) s) hD
  exact (lineSectionZeroIdeal_eq_of_iso
    ((twist_rankOne q _ (hL.pullback p) B).pullback r)
    (twist_rankOne q' _ (hL.pullback p') (pulledBaseLine k B))
    (originalFamilyTwistIso k r hp hq L B) _ _ rfl).symm.trans
      (lineSectionZeroIdeal_pullGlobal r (twist_rankOne q _ (hL.pullback p) B) s hD)

end FLT.Mazur.CartierAbel

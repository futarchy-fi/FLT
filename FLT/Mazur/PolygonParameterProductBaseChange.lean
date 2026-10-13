/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonParameterMarkingBaseChange
public import FLT.Mazur.PolygonParameterProductLine
public import FLT.Mazur.RelativeCartierBaseChangeComposition

/-!
# Successive base change of full translated polygon product markings

The composition chart preserves the full moved Cartier ideal. Its positive-line
comparison therefore preserves the canonical marking section without rescaling.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonParameterTranslation
open PolygonPinching PolygonUniversalAction PolygonMarkingBaseChange FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] translationIso markingIdeal movedMarkingIdeal
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  {T U : Scheme} (g : T ⟶ Spec (.of K)) (k : U ⟶ T)
  (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n)) (a : Fin n → Kˣ)
local notation "H" => Over.pullback k
local notation "δ" => NatTrans.app (Iso.inv (Over.pullbackComp k g)) C
local notation "π" => (pullback.fst (pullback.snd C.hom g) k)

/-- The actual iterated pullback comparison preserves the entire translated product. -/
theorem movedProductMarkingIdeal_baseChange :
    (movedProductMarkingIdeal K n hn p q h (k ≫ g)
      (parameterBaseChange K n g k c) a).comap (δ).left =
        (movedProductMarkingIdeal K n hn p q h g c a).comap π := by
  simp only [movedProductMarkingIdeal, idealSheaf_comap_prod, movedMarkingIdeal_baseChange]

/-- The moved positive-line comparison on the actual iterated pullback chart. -/
irreducible_def movedProductMarkingBaseChangeLineIso :
    (Scheme.Modules.pullback (δ).left).obj
      (movedProductMarkingLine K n hn p q h (k ≫ g) (parameterBaseChange K n g k c) a) ≅
        divisorLineBundle ((movedProductMarkingIdeal K n hn p q h g c a).comap π)
          (relativeCartierBaseChange ((Over.pullback g).obj C).hom k _
            (movedProductMarkingIdeal_cartier K n hn p q h g c a)).1 := by
  let hs := (movedProductMarkingIdeal_cartier K n hn p q h (k ≫ g)
    (parameterBaseChange K n g k c) a).1
  let ht := (relativeCartierBaseChange ((Over.pullback g).obj C).hom k _
    (movedProductMarkingIdeal_cartier K n hn p q h g c a)).1
  let he := movedProductMarkingIdeal_baseChange K n hn p q h g k c a
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- Successive arbitrary base change preserves the moved marking's canonical section exactly. -/
theorem movedProductMarkingBaseChangeLineIso_section :
    DivisorLineSectionCompatible (δ).left
      (movedProductMarkingIdeal_cartier K n hn p q h (k ≫ g)
        (parameterBaseChange K n g k c) a).1
      (relativeCartierBaseChange ((Over.pullback g).obj C).hom k _
        (movedProductMarkingIdeal_cartier K n hn p q h g c a)).1
      (movedProductMarkingBaseChangeLineIso K n hn p q h g k c a) := by
  let hs := (movedProductMarkingIdeal_cartier K n hn p q h (k ≫ g)
    (parameterBaseChange K n g k c) a).1
  let ht := (relativeCartierBaseChange ((Over.pullback g).obj C).hom k _
    (movedProductMarkingIdeal_cartier K n hn p q h g c a)).1
  let he := movedProductMarkingIdeal_baseChange K n hn p q h g k c a
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [movedProductMarkingBaseChangeLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

end FLT.Mazur.PolygonParameterTranslation

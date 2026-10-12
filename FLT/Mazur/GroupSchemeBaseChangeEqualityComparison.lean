/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupSchemeBaseChangeComposition

/-!
# Equality coherence for actual coefficient group comparisons

Iterated pullback preserves a comparison square whose coefficient and source
maps agree. This supplies equality coherence without unfolding pullback groups
or their multiplication operations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GroupSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {S T U : Scheme.{u}} (f : U ⟶ T) (G : CommGrp (Over S))

/-- The actual coefficient comparison, including its original equality of base maps. -/
def equalityComparison {b : T ⟶ S} {k : U ⟶ S} (h : f ≫ b = k)
    {H : CommGrp (Over T)} (e : H ≅ (Over.pullback b).mapCommGrp.obj G) :
    (Over.pullback f).mapCommGrp.obj H ≅ (Over.pullback k).mapCommGrp.obj G :=
  (Over.pullback f).mapCommGrp.mapIso e ≪≫ (compIso f b G).symm ≪≫ congrIso h G

/-- A commuting coefficient comparison remains commuting after arbitrary source pullback. -/
theorem equalityComparison_congr {b₁ b₂ : T ⟶ S} {k₁ k₂ : U ⟶ S}
    (h₁ : f ≫ b₁ = k₁) (h₂ : f ≫ b₂ = k₂)
    {H₁ H₂ : CommGrp (Over T)}
    (e₁ : H₁ ≅ (Over.pullback b₁).mapCommGrp.obj G)
    (e₂ : H₂ ≅ (Over.pullback b₂).mapCommGrp.obj G) (n : H₁ ≅ H₂)
    (hb : b₁ = b₂) (hk : k₁ = k₂) (he : e₁ ≪≫ congrIso hb G = n ≪≫ e₂) :
    equalityComparison f G h₁ e₁ ≪≫ congrIso hk G =
      (Over.pullback f).mapCommGrp.mapIso n ≪≫ equalityComparison f G h₂ e₂ := by
  cases hb
  cases hk
  have he' : e₁ = n ≪≫ e₂ := by
    simpa only [congrIso, eqToIso_refl, Iso.trans_refl] using he
  rw [he']
  simp only [equalityComparison, congrIso, eqToIso_refl, Iso.trans_refl,
    Functor.mapIso_trans, Iso.trans_assoc]

end FLT.Mazur.GroupSchemeBaseChange

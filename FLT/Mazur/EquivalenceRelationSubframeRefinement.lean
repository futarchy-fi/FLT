/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedSubframe

/-!
# Open refinements along arbitrary moving subframes

Restrict an actual subframe selection to independently chosen chart domains.
These morphisms compose for unequal sizes as well as for changes of label.
No invariance of a pulled-back section under the larger permutation group is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J H : Type} [Fintype I] [Fintype J] [Fintype H]
  (o : I) (o' : J) (ι : J ↪ I)
  (U : (source p q I o).Opens) (V : (source p q J o').Opens)
  (hUV : U ≤ subframeMap e o o' ι ⁻¹ᵁ V)

/-- The actual moving subframe morphism on independently restricted charts. -/
def subframeRefinementMap : U.toScheme ⟶ V.toScheme :=
  (subframeMap e o o' ι).resLE V U hUV

/-- The restricted map retains the entire ambient subframe selection. -/
@[reassoc] theorem subframeRefinementMap_inclusion :
    subframeRefinementMap e o o' ι U V hUV ≫ V.ι = U.ι ≫ subframeMap e o o' ι :=
  Scheme.Hom.resLE_comp_ι _ _

variable (o'' : H) (κ : H ↪ J) (Z : (source p q H o'').Opens)
  (hVZ : V ≤ subframeMap e o' o'' κ ⁻¹ᵁ Z)

include hUV hVZ in
/-- Composable open refinements lie in the domain of the composite selection. -/
theorem subframeRefinement_domain_comp :
    U ≤ subframeMap e o o'' (κ.trans ι) ⁻¹ᵁ Z := by
  rw [← subframeMap_comp e o o' o'' ι κ, Scheme.Hom.comp_preimage]
  exact hUV.trans ((subframeMap e o o' ι).preimage_mono hVZ)

/-- The actual chart morphisms compose, including strict nested subframes. -/
@[reassoc] theorem subframeRefinementMap_comp
    (hUZ : U ≤ subframeMap e o o'' (κ.trans ι) ⁻¹ᵁ Z) :
    subframeRefinementMap e o o' ι U V hUV ≫
      subframeRefinementMap e o' o'' κ V Z hVZ =
        subframeRefinementMap e o o'' (κ.trans ι) U Z hUZ := by
  apply (cancel_mono Z.ι).mp
  simp only [Category.assoc, subframeRefinementMap_inclusion,
    subframeRefinementMap_inclusion_assoc, subframeMap_comp]

/-- Pullback of actual functions respects the same nested chart selections. -/
theorem subframeRefinement_appTop_comp
    (hUZ : U ≤ subframeMap e o o'' (κ.trans ι) ⁻¹ᵁ Z) (w : Γ(Z.toScheme, ⊤)) :
    (subframeRefinementMap e o o' ι U V hUV).appTop
      ((subframeRefinementMap e o' o'' κ V Z hVZ).appTop w) =
        (subframeRefinementMap e o o'' (κ.trans ι) U Z hUZ).appTop w := by
  change ((subframeRefinementMap e o o' ι U V hUV ≫
    subframeRefinementMap e o' o'' κ V Z hVZ).appTop w) = _
  rw [subframeRefinementMap_comp e o o' ι U V hUV o'' κ Z hVZ hUZ]

end FLT.Mazur.EquivalenceRelationNormalizedFrames

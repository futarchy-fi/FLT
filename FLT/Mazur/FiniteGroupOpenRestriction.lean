/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Restricting group actions to stable opens

The group law is proved for the actual restricted scheme automorphisms.
Inclusions of stable opens are equivariant, supplying the overlap maps for
invariant affine charts.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteGroupRestriction

variable {G : Type*} [Group G] {X : Scheme} (ρ : G →* Aut X)
variable (U : X.Opens) (hU : ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U)

/-- Restrict a single automorphism to the stable open subscheme. -/
def restrictedAut (g : G) : Aut U.toScheme :=
  X.isoOfEq (hU g).symm ≪≫ (ρ g).hom.preimageIso U

/-- The inclusion intertwines the restricted and original automorphisms. -/
@[reassoc (attr := simp)]
lemma restrictedAut_hom_ι (g : G) :
    (restrictedAut ρ U hU g).hom ≫ U.ι = U.ι ≫ (ρ g).hom := by
  simp [restrictedAut]

/-- The genuine group action on a stable open subscheme. -/
def restrictedAction : G →* Aut U.toScheme where
  toFun := restrictedAut ρ U hU
  map_one' := by
    apply Aut.ext
    rw [← cancel_mono U.ι]
    rw [restrictedAut_hom_ι, map_one]
    change U.ι ≫ 𝟙 X = 𝟙 U.toScheme ≫ U.ι
    simp
  map_mul' g h := by
    apply Aut.ext
    rw [← cancel_mono U.ι]
    simp [Aut.Aut_mul_def, Category.assoc]

/-- The restricted action commutes with the open immersion into the original scheme. -/
@[reassoc]
lemma restrictedAction_hom_ι (g : G) :
    (restrictedAction ρ U hU g).hom ≫ U.ι = U.ι ≫ (ρ g).hom :=
  restrictedAut_hom_ι ρ U hU g

/-- Inclusions between stable opens are equivariant for the constructed actions. -/
@[reassoc]
lemma inclusion_equivariant (V : X.Opens) (hV : ∀ g : G, (ρ g).hom ⁻¹ᵁ V = V)
    (e : V ≤ U) (g : G) :
    X.homOfLE e ≫ (restrictedAction ρ U hU g).hom =
      (restrictedAction ρ V hV g).hom ≫ X.homOfLE e := by
  apply (cancel_mono U.ι).mp
  calc
    (X.homOfLE e ≫ (restrictedAction ρ U hU g).hom) ≫ U.ι =
        X.homOfLE e ≫ (U.ι ≫ (ρ g).hom) := by
      rw [Category.assoc, restrictedAction_hom_ι]
    _ = V.ι ≫ (ρ g).hom := by rw [← Category.assoc, Scheme.homOfLE_ι]
    _ = ((restrictedAction ρ V hV g).hom ≫ X.homOfLE e) ≫ U.ι := by
      rw [Category.assoc, Scheme.homOfLE_ι, restrictedAction_hom_ι]

end FLT.Mazur.FiniteGroupRestriction

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeQuotientAffineFlatComparison
public import FLT.Mazur.FiniteGroupQuotientDescent

/-!
# Arbitrary-target descent after affine flat base change

The tensor comparison transports the full fixed-ring universal property to
the actual pullback scheme. The new-base projection is an epimorphism, and
every invariant map to an arbitrary scheme descends uniquely through it.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open FLT.Mazur.SchemeCoordinateAction

namespace FLT.Mazur.SchemeQuotientAffineBase

universe u
variable {G : Type u} [Group G] [Finite G] {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
variable (ρ : G →* Aut X) (f : S ⟶ SchemeFiniteGroupQuotient.quotient ρ) [Flat f]

attribute [local instance] FiniteGroupQuotient.tensorAction

/-- The actual affine flat pullback projection is an epimorphism for all scheme targets. -/
instance pullback_snd_epi : Epi (pullback.snd (SchemeFiniteGroupQuotient.quotientMap ρ) f) := by
  let _ := coordinateAlgebra ρ f
  let _ := coordinateAction ρ
  constructor
  intro Y a b hab
  rw [← cancel_epi (quotientIso ρ f).hom]
  apply (cancel_epi (FiniteGroupQuotient.quotientMap G
    (Γ(S, ⊤) ⊗[SchemeFiniteGroupQuotient.invariantCoordinates ρ] Γ(X, ⊤)))).mp
  rw [← Category.assoc, ← Category.assoc, quotientMap_quotientIso_hom,
    ← iso_hom_snd, Category.assoc, Category.assoc, hab]

variable {Y : Scheme.{u}} (k : pullback (SchemeFiniteGroupQuotient.quotientMap ρ) f ⟶ Y)
variable (hk : ∀ g : G,
  (FiniteGroupPullback.action ρ _ (SchemeFiniteGroupQuotient.quotientMap_invariant ρ) f g).hom ≫
    k = k)

include hk in
omit [Finite G] [Flat f] in
/-- The actual tensor model of an invariant map is invariant under the tensor ring action. -/
lemma model_invariant (g : G) :
    let _ := coordinateAlgebra ρ f
    let _ := coordinateAction ρ
    FiniteGroupQuotient.actionMap G
      (Γ(S, ⊤) ⊗[SchemeFiniteGroupQuotient.invariantCoordinates ρ] Γ(X, ⊤)) g ≫
        (iso ρ f).hom ≫ k = (iso ρ f).hom ≫ k := by
  let _ := coordinateAlgebra ρ f
  let _ := coordinateAction ρ
  dsimp only
  rw [iso_equivariant_assoc, hk]

/-- The actual descended morphism on the new affine base. -/
def desc : S ⟶ Y :=
  let _ := coordinateAlgebra ρ f
  let _ := coordinateAction ρ
  (quotientIso ρ f).inv ≫ FiniteGroupQuotient.desc G
    (Γ(S, ⊤) ⊗[SchemeFiniteGroupQuotient.invariantCoordinates ρ] Γ(X, ⊤))
    ((iso ρ f).hom ≫ k) (model_invariant ρ f k hk)

/-- The descended map factors the original invariant map on the actual pullback. -/
@[reassoc]
lemma desc_fac : pullback.snd (SchemeFiniteGroupQuotient.quotientMap ρ) f ≫
    desc ρ f k hk = k := by
  let _ := coordinateAlgebra ρ f
  let _ := coordinateAction ρ
  rw [← cancel_epi (iso ρ f).hom, ← Category.assoc, iso_hom_snd]
  unfold desc
  rw [← quotientMap_quotientIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
    FiniteGroupQuotient.desc_fac]

include hk in
/-- Every invariant morphism descends uniquely after flat base change between affine schemes. -/
theorem existsUnique_desc : ∃! d : S ⟶ Y,
    pullback.snd (SchemeFiniteGroupQuotient.quotientMap ρ) f ≫ d = k := by
  refine ⟨desc ρ f k hk, desc_fac ρ f k hk, ?_⟩
  intro d hd
  rw [← cancel_epi (pullback.snd (SchemeFiniteGroupQuotient.quotientMap ρ) f), hd, desc_fac]

end FLT.Mazur.SchemeQuotientAffineBase

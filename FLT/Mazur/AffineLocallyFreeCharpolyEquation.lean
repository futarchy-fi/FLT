/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCharpolyPolynomial

/-!
# Cayley-Hamilton on the whole locally free source

The polynomial glued from independent finite free charts annihilates the
original global source section. This equation uses the original structure
sheaf and remains valid when the local ranks are different.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial
namespace FLT.Mazur.AffineCharpolyCoefficientGluing
universe u v w
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [IsAffine Y]
  {ι : Type v} (U : ι → Y.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis f (U i)) (hcover : ⨆ i, (U i).1 = ⊤)

/-- Local Cayley-Hamilton descends to an equation in the entire original source. -/
theorem polynomial_equation (s : Γ(X, ⊤)) :
    (polynomial f U hU hcover s).eval₂ f.appTop.hom s = 0 := by
  apply X.sheaf.eq_of_locally_eq' (fun i ↦ f ⁻¹ᵁ (U i).1) ⊤
    (fun _ ↦ homOfLE le_top) (ge_of_eq (f.iSup_preimage_eq_top hcover))
  intro i
  change X.presheaf.map (homOfLE (show f ⁻¹ᵁ (U i).1 ≤ ⊤ from le_top)).op
    ((polynomial f U hU hcover s).eval₂ f.appTop.hom s) = _
  apply (ConcreteCategory.bijective_of_isIso (f ⁻¹ᵁ (U i).1).topIso.inv).injective
  rw [AffineNormGluing.topIso_inv_global, map_zero, map_zero]
  have hc : (f ⁻¹ᵁ (U i).1).ι.appTop.hom.comp f.appTop.hom =
      (f ∣_ (U i).1).appTop.hom.comp (U i).1.ι.appTop.hom := by
    ext t
    exact congrArg (fun k : (f ⁻¹ᵁ (U i).1).toScheme ⟶ Y ↦ k.appTop t)
      (morphismRestrict_ι f (U i).1).symm
  change (f ⁻¹ᵁ (U i).1).ι.appTop.hom
    ((polynomial f U hU hcover s).eval₂ f.appTop.hom s) = 0
  rw [hom_eval₂, hc, ← eval₂_map, polynomial_top f U hU hcover (U i) (hU i)]
  exact (AffineChosenBasisCharpoly.equation (f ∣_ (U i).1) (hU i) _).2

variable {P T : Scheme.{u}} [IsAffine T] {a : P ⟶ X} {b : P ⟶ T} {g : T ⟶ Y}
  [IsAffineHom b] (H : IsPullback a b f g)

include H in
/-- The entire glued polynomial commutes with arbitrary affine cartesian base change. -/
theorem polynomial_pullback {κ : Type w} (V : κ → T.affineOpens)
    (hV : ∀ j, AffineOpenNorm.HasBasis b (V j)) (hcoverV : ⨆ j, (V j).1 = ⊤)
    (s : Γ(X, ⊤)) :
    polynomial b V hV hcoverV (a.appTop s) =
      (polynomial f U hU hcover s).map g.appTop.hom := by
  ext n
  rw [coeff_map, polynomial_coeff, polynomial_coeff]
  exact coefficient_pullback_any H U hU hcover V hV hcoverV s n

end FLT.Mazur.AffineCharpolyCoefficientGluing

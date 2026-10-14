/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearActionDomain
public import FLT.Mazur.WeierstrassCoefficientShearTransport

/-!
# Coefficient overlap transport of the full smooth action domain

The two original inputs descend together. Their domain is cartesian over the
original integral domain, so overlap transport retains the full integral pair.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
local notation "f" => integralSmoothStructure (W.map (algebraMap R S))
local notation "g" => coefficientShearGluedStructure hπ data S r j hj
local notation "p" => coefficientShearGluedProjection hπ data S r j hj
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "P" => coefficientShearOriginalActionProduct hπ data S r j hj
local notation "d" => pullback.fst f g ≫ f
local notation "d₀" => pullback.snd (integralSmoothStructure W) base ≫ base

/-- The complete two-input domain is the coefficient pullback of the integral domain. -/
theorem coefficientShearActionDomain_coefficient_isPullback : IsPullback P d d₀ q := by
  have H := (coefficientShearOriginalActionProduct_isPullback
    hπ data S r j hj).paste_vert (coefficientShearGlued_isPullback hπ data S r j hj).flip
  simpa only [pullback.condition] using H

local notation "H" => coefficientShearActionDomain_coefficient_isPullback hπ data S r j hj
variable {T : Scheme.{u}} (a b : T ⟶ Spec (.of S))
  (h : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
    b ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- Transport both complete inputs across any coefficient overlap. -/
def coefficientShearActionDomainTransport : pullback a d ≅ pullback b d :=
  CartesianCoefficientTransport.iso H a b h

/-- The coefficient overlap projection is retained by domain transport. -/
@[reassoc] theorem coefficientShearActionDomainTransport_structure :
    (coefficientShearActionDomainTransport hπ data S r j hj a b h).hom ≫
      pullback.fst b d = pullback.fst a d :=
  CartesianCoefficientTransport.map_coefficient H a b h

/-- Domain transport preserves the entire original integral input pair. -/
@[reassoc] theorem coefficientShearActionDomainTransport_original :
    (coefficientShearActionDomainTransport hπ data S r j hj a b h).hom ≫
      pullback.snd b d ≫ P = pullback.snd a d ≫ P :=
  CartesianCoefficientTransport.map_original H a b h

/-- The full smooth input is retained after projection to its original coefficient curve. -/
@[reassoc] theorem coefficientShearActionDomainTransport_parameter :
    (coefficientShearActionDomainTransport hπ data S r j hj a b h).hom ≫
      pullback.snd b d ≫ pullback.fst f g ≫ originalSmoothCoefficientMap S W =
      pullback.snd a d ≫ pullback.fst f g ≫ originalSmoothCoefficientMap S W := by
  rw [← coefficientShearOriginalActionProduct_parameter,
    coefficientShearActionDomainTransport_original_assoc,
    coefficientShearOriginalActionProduct_parameter]

/-- The whole model input is retained after projection to the original integral model. -/
@[reassoc] theorem coefficientShearActionDomainTransport_model :
    (coefficientShearActionDomainTransport hπ data S r j hj a b h).hom ≫
      pullback.snd b d ≫ pullback.snd f g ≫ p =
      pullback.snd a d ≫ pullback.snd f g ≫ p := by
  rw [← coefficientShearOriginalActionProduct_model,
    coefficientShearActionDomainTransport_original_assoc,
    coefficientShearOriginalActionProduct_model]

/-- Transport of the original pair satisfies the actual triple-overlap cocycle. -/
@[reassoc] theorem coefficientShearActionDomainTransport_comp (c : T ⟶ Spec (.of S))
    (hb : b ≫ q = c ≫ q) :
    (coefficientShearActionDomainTransport hπ data S r j hj a b h).hom ≫
        (coefficientShearActionDomainTransport hπ data S r j hj b c hb).hom =
      (coefficientShearActionDomainTransport hπ data S r j hj a c (h.trans hb)).hom :=
  CartesianCoefficientTransport.map_comp H a b h c hb

/-- Repeated coefficient lifts act by the identity on both full inputs. -/
theorem coefficientShearActionDomainTransport_self :
    (coefficientShearActionDomainTransport hπ data S r j hj a a rfl).hom = 𝟙 _ :=
  CartesianCoefficientTransport.map_self H a

end FLT.Mazur.WeierstrassDividedDepth

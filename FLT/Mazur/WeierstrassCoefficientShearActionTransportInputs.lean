/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearActionDomainTransport

/-!
# Both original action inputs commute with coefficient transport

Projection from the transported domain agrees with the full smooth-parameter
and full model transports, as morphisms of their actual overlap schemes.
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
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "d" => pullback.fst f g ≫ f
local notation "H" => coefficientShearActionDomain_coefficient_isPullback hπ data S r j hj
variable {T : Scheme.{u}} (a : T ⟶ Spec (.of S))

/-- The full smooth-parameter projection on each actual coefficient overlap. -/
def coefficientShearOverlapParameter : pullback a d ⟶ pullback a f :=
  CartesianCoefficientTransport.objectMap a (pullback.fst f g) rfl

/-- The full model projection on each actual coefficient overlap. -/
def coefficientShearOverlapModel : pullback a d ⟶ pullback a g :=
  CartesianCoefficientTransport.objectMap a (pullback.snd f g) pullback.condition.symm

/-- The overlap parameter retains its entire original smooth scheme map. -/
@[reassoc] theorem coefficientShearOverlapParameter_parameter :
    coefficientShearOverlapParameter hπ data S r j hj a ≫ pullback.snd a f =
      pullback.snd a d ≫ pullback.fst f g :=
  CartesianCoefficientTransport.objectMap_object _ _ _

/-- The overlap model projection retains the entire original equation model. -/
@[reassoc] theorem coefficientShearOverlapModel_model :
    coefficientShearOverlapModel hπ data S r j hj a ≫ pullback.snd a g =
      pullback.snd a d ≫ pullback.snd f g :=
  CartesianCoefficientTransport.objectMap_object _ _ _

variable (b : T ⟶ Spec (.of S))
  (h : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
    b ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- Domain transport intertwines the independently constructed full smooth-parameter transport. -/
@[reassoc] theorem coefficientShearActionDomainTransport_parameter_transport :
    (coefficientShearActionDomainTransport hπ data S r j hj a b h).hom ≫
        coefficientShearOverlapParameter hπ data S r j hj b =
      coefficientShearOverlapParameter hπ data S r j hj a ≫
        (CartesianCoefficientTransport.iso (originalSmoothCoefficientMap_isPullback S W)
          a b h).hom :=
  CartesianCoefficientTransport.map_naturality H a b h
    (originalSmoothCoefficientMap_isPullback S W) (pullback.fst f g)
    (pullback.fst (integralSmoothStructure W) base)
    (coefficientShearOriginalActionProduct_parameter hπ data S r j hj).symm rfl

/-- Domain transport intertwines the full equation-model transport on every overlap. -/
@[reassoc] theorem coefficientShearActionDomainTransport_model_transport :
    (coefficientShearActionDomainTransport hπ data S r j hj a b h).hom ≫
        coefficientShearOverlapModel hπ data S r j hj b =
      coefficientShearOverlapModel hπ data S r j hj a ≫
        (coefficientShearTransport hπ data S r j hj a b h).hom :=
  CartesianCoefficientTransport.map_naturality H a b h
    (coefficientShearGlued_isPullback hπ data S r j hj).flip (pullback.snd f g)
    (pullback.snd (integralSmoothStructure W) base)
    (coefficientShearOriginalActionProduct_model hπ data S r j hj).symm pullback.condition.symm

end FLT.Mazur.WeierstrassDividedDepth

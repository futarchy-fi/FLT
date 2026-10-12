/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentTransport

/-!
# Compatibility of the original action with tangent overlap transport

Transport the genuine smooth-parameter action domain, preserving both
original inputs. Its action commutes with the model comparison over every
overlap, in particular the actual quadratic Cech scheme.
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
  (j : ℕ) (hj : j ≤ n)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "q" => nodeTangentCover W
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "ys" => pullback.fst q base
local notation "yx" => pullback.snd q base
local notation "f" => integralSmoothStructure W
local notation "fS" => integralSmoothStructure (W.map (algebraMap R S))
local notation "ds" => pullback.snd fS ys ≫ ys
local notation "c" => finiteGlobalCoefficientActionProduct hπ data j hj S
local notation "a" => finiteGlobalCoefficientAction hπ data j hj S
variable {T : Scheme.{u}} (r t : T ⟶ Spec (.of (AdjoinRoot (nodeTangentPolynomial W))))
  (h : r ≫ nodeTangentCover W = t ≫ nodeTangentCover W)

/-- The actual action domain is transported through its proved Cartesian coefficient square. -/
def finiteGlobalTangentDomainTransport : pullback r ds ≅ pullback t ds :=
  CartesianCoefficientTransport.iso
    (finiteGlobalCoefficientDomain_isPullback hπ data j hj S) r t h

@[reassoc] theorem finiteGlobalTangentDomainTransport_structure :
    (finiteGlobalTangentDomainTransport hπ data j hj r t h).hom ≫ pullback.fst t ds =
      pullback.fst r ds := CartesianCoefficientTransport.map_coefficient _ _ _ h

/-- The pair of original action inputs survives transport unchanged. -/
@[reassoc] theorem finiteGlobalTangentDomainTransport_projection :
    (finiteGlobalTangentDomainTransport hπ data j hj r t h).hom ≫ pullback.snd t ds ≫ c =
      pullback.snd r ds ≫ c := CartesianCoefficientTransport.map_original _ _ _ h

/-- In particular, transport retains the original smooth parameter, not just the model input. -/
@[reassoc] theorem finiteGlobalTangentDomainTransport_parameter :
    (finiteGlobalTangentDomainTransport hπ data j hj r t h).hom ≫
        pullback.snd t ds ≫ pullback.fst fS ys ≫ originalSmoothCoefficientMap S W =
      pullback.snd r ds ≫ pullback.fst fS ys ≫ originalSmoothCoefficientMap S W := by
  erw [← finiteGlobalCoefficientActionProduct_fst hπ data j hj S,
    finiteGlobalTangentDomainTransport_projection_assoc]

/-- The original coefficient action is over the same chosen coefficient lift as its domain. -/
theorem finiteGlobalTangentAction_coefficient : a ≫ ys = ds := by
  exact (finiteGlobalCoefficientAction_structure hπ data j hj S).trans pullback.condition

/-- Pull the original action back to one of the coefficient lifts on an overlap. -/
def finiteGlobalTangentOverlapAction : pullback r ds ⟶ pullback r ys :=
  CartesianCoefficientTransport.objectMap r a
    (finiteGlobalTangentAction_coefficient hπ data j hj)

/-- The pulled action retains the exact original action result on the integral model. -/
@[reassoc] theorem finiteGlobalTangentOverlapAction_projection :
    finiteGlobalTangentOverlapAction hπ data j hj r ≫ pullback.snd r ys ≫ yx =
      pullback.snd r ds ≫ c ≫ finiteGlobalAction hπ data j hj := by
  rw [finiteGlobalTangentOverlapAction, CartesianCoefficientTransport.objectMap_object_assoc]
  exact congrArg (pullback.snd r ds ≫ ·)
    (finiteGlobalCoefficientAction_projection hπ data j hj S)

/-- The actual two-input action commutes with finite-model transport on the whole overlap. -/
@[reassoc] theorem finiteGlobalTangentTransport_action :
    (finiteGlobalTangentDomainTransport hπ data j hj r t h).hom ≫
        finiteGlobalTangentOverlapAction hπ data j hj t =
      finiteGlobalTangentOverlapAction hπ data j hj r ≫
        (finiteGlobalTangentTransport hπ data j hj r t h).hom :=
  CartesianCoefficientTransport.map_naturality
    (finiteGlobalCoefficientDomain_isPullback hπ data j hj S) r t h
    (IsPullback.of_hasPullback q base).flip a (finiteGlobalAction hπ data j hj)
    (finiteGlobalCoefficientAction_projection hπ data j hj S)
    (finiteGlobalTangentAction_coefficient hπ data j hj)

/-- The domain transports themselves satisfy the cocycle with both inputs retained. -/
@[reassoc] theorem finiteGlobalTangentDomainTransport_comp
    (w : T ⟶ Spec (.of (AdjoinRoot (nodeTangentPolynomial W))))
    (ht : t ≫ nodeTangentCover W = w ≫ nodeTangentCover W) :
    (finiteGlobalTangentDomainTransport hπ data j hj r t h).hom ≫
        (finiteGlobalTangentDomainTransport hπ data j hj t w ht).hom =
      (finiteGlobalTangentDomainTransport hπ data j hj r w (h.trans ht)).hom :=
  CartesianCoefficientTransport.map_comp _ _ _ h _ ht

omit r t h in
/-- Compatibility with the previously constructed comparison on the genuine Cech overlap. -/
theorem finiteGlobalTangentCechIso_action :
    (finiteGlobalTangentDomainTransport hπ data j hj (pullback.fst q q) (pullback.snd q q)
        pullback.condition).hom ≫
        finiteGlobalTangentOverlapAction hπ data j hj (pullback.snd q q) =
      finiteGlobalTangentOverlapAction hπ data j hj (pullback.fst q q) ≫
        (finiteGlobalTangentCechIso hπ data j hj).hom := by
  rw [finiteGlobalTangentCechIso_eq_transport]
  exact finiteGlobalTangentTransport_action hπ data j hj _ _ pullback.condition

end FLT.Mazur.WeierstrassDividedDepth

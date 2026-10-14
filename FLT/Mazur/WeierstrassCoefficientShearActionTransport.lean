/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearActionDomainTransport
public import FLT.Mazur.WeierstrassCoefficientShearAction

/-!
# The complete smooth action commutes with coefficient overlap transport

The action on each overlap is induced by the original full action morphism.
Naturality of cartesian transport proves its compatibility with descent.
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
local notation "P" => coefficientShearOriginalActionProduct hπ data S r j hj
local notation "d" => pullback.fst f g ≫ f
local notation "A" => coefficientShearAction hπ data S r j hj
local notation "H" => coefficientShearActionDomain_coefficient_isPullback hπ data S r j hj
local notation "H₀" => IsPullback.flip (coefficientShearGlued_isPullback hπ data S r j hj)
variable {T : Scheme.{u}} (a : T ⟶ Spec (.of S))

/-- The original full smooth action on the actual coefficient overlap. -/
def coefficientShearOverlapAction : pullback a d ⟶ pullback a g :=
  CartesianCoefficientTransport.objectMap a A
    (coefficientShearAction_structure hπ data S r j hj)

/-- The overlap action leaves its coefficient input unchanged. -/
@[reassoc] theorem coefficientShearOverlapAction_structure :
    coefficientShearOverlapAction hπ data S r j hj a ≫ pullback.fst a g =
      pullback.fst a d := CartesianCoefficientTransport.objectMap_coefficient _ _ _

/-- The overlap action retains the entire independently constructed equation action. -/
@[reassoc] theorem coefficientShearOverlapAction_model :
    coefficientShearOverlapAction hπ data S r j hj a ≫ pullback.snd a g =
      pullback.snd a d ≫ A := CartesianCoefficientTransport.objectMap_object _ _ _

/-- Its integral projection is the original action on the complete original pair. -/
@[reassoc] theorem coefficientShearOverlapAction_original :
    coefficientShearOverlapAction hπ data S r j hj a ≫ pullback.snd a g ≫ p =
      pullback.snd a d ≫ P ≫ finiteGlobalAction hπ data j hj := by
  rw [coefficientShearOverlapAction_model_assoc, coefficientShearAction_projection]

variable (b : T ⟶ Spec (.of S))
  (h : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
    b ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- The complete equation action respects the actual two-input descent comparison. -/
@[reassoc] theorem coefficientShearAction_transport :
    (coefficientShearActionDomainTransport hπ data S r j hj a b h).hom ≫
        coefficientShearOverlapAction hπ data S r j hj b =
      coefficientShearOverlapAction hπ data S r j hj a ≫
        (coefficientShearTransport hπ data S r j hj a b h).hom :=
  CartesianCoefficientTransport.map_naturality H a b h H₀ A
    (finiteGlobalAction hπ data j hj) (coefficientShearAction_projection hπ data S r j hj)
    (coefficientShearAction_structure hπ data S r j hj)

end FLT.Mazur.WeierstrassDividedDepth

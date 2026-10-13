/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearScaleOne
public import FLT.Mazur.PrincipalOpenTransportGeometry
public import FLT.Mazur.PrincipalOpenTensorGeometry

/-!
# The full shifted infinity boundary of the scale-one incidence chart

Transport the entire original vertical localization through the slope equivalence.
The vertical function retains the chosen root shift, including on the full boundary.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S s = 1) (h3 : algebraMap R S b3 = 0)
  (h4 : algebraMap R S b4 = 0) (h6 : algebraMap R S b6 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "P" => SlopeOpen a
local notation "T₀" => S ⊗[R] Coordinate W s b3 b4 b6
local notation "e" => tensorShearScaleOneEquiv W s b3 b4 b6 S r hs h3 h4 h6 hr
local notation "z" => (slopeZ a * (slopeZ a + algebraMap S P a)) *
  (slopeZ a + algebraMap S P r)
local notation "y₀" => (1 : S) ⊗ₜ[R] y W s b3 b4 b6

/-- The full original vertical boundary is the root-shifted open of the whole slope chart. -/
def tensorShearScaleOneInfinityEquiv :
    Localization.Away y₀ ≃ₐ[S] Localization.Away z :=
  PrincipalOpenTransport.equiv (A := T₀) e y₀ z
    (tensorShearScaleOneEquiv_y W s b3 b4 b6 S r hs h3 h4 h6 hr)

/-- Every original tensor function is preserved on the entire shifted infinity boundary. -/
theorem tensorShearScaleOneInfinityEquiv_base (w : T₀) :
    tensorShearScaleOneInfinityEquiv W s b3 b4 b6 S r hs h3 h4 h6 hr
      (algebraMap T₀ (Localization.Away y₀) w) =
        algebraMap P (Localization.Away z) (e w) :=
  PrincipalOpenTransport.equiv_base _ _ _ _ w

/-- The spectrum of the entire original vertical localization in shifted slope coordinates. -/
def tensorShearScaleOneInfinityIso :
    Spec (.of (Localization.Away z)) ≅ Spec (.of (Localization.Away y₀)) :=
  Scheme.Spec.mapIso (tensorShearScaleOneInfinityEquiv W s b3 b4 b6 S r
    hs h3 h4 h6 hr).toRingEquiv.toCommRingCatIso.op

/-- The full boundary inclusion is the original slope comparison restricted to that open. -/
@[reassoc] theorem tensorShearScaleOneInfinityIso_inclusion :
    (tensorShearScaleOneInfinityIso W s b3 b4 b6 S r hs h3 h4 h6 hr).hom ≫
      PrincipalOpenTensor.inclusion S (y W s b3 b4 b6) =
        PrincipalOpenTransport.inclusion z ≫
          (Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext
    (RingHom.ext (tensorShearScaleOneInfinityEquiv_base W s b3 b4 b6 S r hs h3 h4 h6 hr))

end FLT.Mazur.WeierstrassModificationX

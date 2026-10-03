/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ConnectingRestrictionNaturality
public import FLT.LocalClassFieldTheory.IntegralH2Characters

/-!
# Restriction of the rational-circle description of integral H2

The identity on trivial coefficients gives the group restriction map.
Character pullback commutes with the positive integral connecting isomorphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory HomologicalComplex

attribute [local instance] trivialCoefficientAction trivialCoefficientIntComm
  trivialCoefficientContinuous rationalCoefficientTopology rationalCoefficientDiscrete
  rationalCircleCoefficientTopology rationalCircleCoefficientDiscrete

variable {G H : Type} [Group G] [Group H]

/-- Identity coefficients intertwine the restricted trivial action. -/
def trivialRestrictionCoefficient (f : G →* H) (A : Type) [AddCommGroup A] :
    Rep.res f (Rep.of (Representation.ofDistribMulAction ℤ H A)) ⟶
      Rep.of (Representation.ofDistribMulAction ℤ G A) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [TotallyDisconnectedSpace H]

/-- Continuous restriction for trivial integral coefficient modules. -/
def trivialRestriction (f : G →ₜ* H) (A : Type) [AddCommGroup A]
    [TopologicalSpace A] [DiscreteTopology A] :
    continuousCochains ℤ H A ⟶ continuousCochains ℤ G A :=
  continuousRestriction f.toMonoidHom f.continuous (trivialRestrictionCoefficient f.toMonoidHom A)

/-- The H1 character class pulls back along the continuous group homomorphism. -/
theorem trivialRestriction_character (f : G →ₜ* H) {A : Type} [AddCommGroup A]
    [TopologicalSpace A] [DiscreteTopology A] (χ : H →ₜ* Multiplicative A) :
    (homologyMap (trivialRestriction f A) 1).hom
        (integralH1Class (k := ℤ) (characterCocycle χ)) =
      integralH1Class (k := ℤ) (characterCocycle (χ.comp f)) := by
  unfold integralH1Class
  apply cochainHomologyClass_map

/-- The rational-integral connecting square for pure group restriction. -/
theorem rationalIntegralConnectingMap_restriction (f : G →ₜ* H) (n : ℕ) :
    rationalIntegralConnectingMap H n ≫ homologyMap (trivialRestriction f ℤ) (n + 1) =
      homologyMap (trivialRestriction f (AddCircle (1 : ℚ))) n ≫
        rationalIntegralConnectingMap G n :=
  continuousConnectingMap_restriction_naturality
    (integralRationalInclusion H) (rationalCircleProjection H) (integralRational_comp_projection H)
    (integralRationalInclusion G) (rationalCircleProjection G) (integralRational_comp_projection G)
    f.toMonoidHom f.continuous (trivialRestrictionCoefficient f.toMonoidHom ℤ)
    (trivialRestrictionCoefficient f.toMonoidHom ℚ)
    (trivialRestrictionCoefficient f.toMonoidHom (AddCircle (1 : ℚ)))
    (fun _ => rfl) (fun _ => rfl)
    (integralRationalInclusion_injective H) (rationalCircleProjection_surjective H)
    (rationalCircleProjection_kernel H)
    (integralRationalInclusion_injective G) (rationalCircleProjection_surjective G)
    (rationalCircleProjection_kernel G) n

/-- The integral H2 character equivalence is natural under continuous group restriction. -/
theorem integralH2CharacterEquiv_restriction (f : G →ₜ* H)
    (χ : H →ₜ* Multiplicative (AddCircle (1 : ℚ))) :
    (homologyMap (trivialRestriction f ℤ) 2).hom (integralH2CharacterEquiv H χ) =
      integralH2CharacterEquiv G (χ.comp f) := by
  rw [integralH2CharacterEquiv_apply, integralH2CharacterEquiv_apply]
  have h := congrArg (fun t => t.hom (integralH1Class (k := ℤ) (characterCocycle χ)))
    (rationalIntegralConnectingMap_restriction f 1)
  change _ = (rationalIntegralConnectingMap G 1).hom
    ((homologyMap (trivialRestriction f (AddCircle (1 : ℚ))) 1).hom
      (integralH1Class (k := ℤ) (characterCocycle χ))) at h
  rw [trivialRestriction_character] at h
  exact h

end LocalClassFieldTheory

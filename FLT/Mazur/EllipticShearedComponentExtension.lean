/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticShearDescent
public import FLT.Mazur.EllipticComponentBaseChange

/-!
# Component extension into an explicitly identified sheared model

Compose actual component base change with inverse integral shearing.
The resulting injection has fixed image under a compatible tangent action
when the base field and shear satisfy the explicit conjugation identities.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {L : Type*} [Field L] [DecidableEq L]
  (B : ValuationSubring L) (V : WeierstrassCurve B) (s : B)
  (S : WeierstrassCurve B) (hS : S = integralRootShear B s • V)
  [(V.map (algebraMap B L)).IsElliptic]

/-- Inverse integral shearing with an explicitly identified target model. -/
noncomputable def shearedProjectiveEquiv :
    (V.map (algebraMap B L)).toProjective.Point ≃+
      (S.map (algebraMap B L)).toProjective.Point := by
  subst S
  exact (integralProjectiveVariableChange B V (integralRootShear B s)).symm

/-- Inverse integral shearing on actual component quotients. -/
noncomputable def shearedComponentEquiv :
    EllipticComponentQuotient B V ≃+ EllipticComponentQuotient B S := by
  subst S
  exact (integralComponentVariableChange B V (integralRootShear B s)).symm

/-- The component equivalence is induced by the point equivalence. -/
theorem shearedComponentEquiv_mk (P : (V.map (algebraMap B L)).toProjective.Point) :
    shearedComponentEquiv B V s S hS (ellipticComponentHom B V P) =
      ellipticComponentHom B S (shearedProjectiveEquiv B V s S hS P) := by
  subst S
  apply (integralComponentVariableChange B V (integralRootShear B s)).injective
  rw [show shearedComponentEquiv B V s (integralRootShear B s • V) rfl =
    (integralComponentVariableChange B V (integralRootShear B s)).symm from rfl,
    AddEquiv.apply_symm_apply, integralComponentVariableChange_mk]
  change _ = ellipticComponentHom B V
    (integralProjectiveVariableChange B V (integralRootShear B s)
      ((integralProjectiveVariableChange B V (integralRootShear B s)).symm P))
  rw [AddEquiv.apply_symm_apply]

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (f : K →+* L) (g : A →+* B) [IsLocalHom g]
  (hc : (algebraMap B L).comp g = f.comp (algebraMap A K))
  [(W.map g |>.map (algebraMap B L)).IsElliptic]

/-- The rational component injection into the split model after inverse shearing. -/
noncomputable def shearedComponentExtension
    (h : S = integralRootShear B s • W.map g) :
    EllipticComponentQuotient A W →+ EllipticComponentQuotient B S :=
  (shearedComponentEquiv B (W.map g) s S h).toAddMonoidHom.comp
    (integralComponentExtension A B W f g hc)

/-- Inverse shearing retains the injectivity of actual component extension. -/
theorem shearedComponentExtension_injective
    (h : S = integralRootShear B s • W.map g) :
    Function.Injective (shearedComponentExtension B s S A W f g hc h) :=
  (shearedComponentEquiv B (W.map g) s S h).injective.comp
    (integralComponentExtension_injective A B W f g hc)

/-- The sheared component injection sends each rational point to its sheared extension. -/
theorem shearedComponentExtension_mk (h : S = integralRootShear B s • W.map g)
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    shearedComponentExtension B s S A W f g hc h (ellipticComponentHom A W P) =
      ellipticComponentHom B S (shearedProjectiveEquiv B (W.map g) s S h
        (integralProjectiveExtension A B W f g hc P)) :=
  shearedComponentEquiv_mk B (W.map g) s S h _

variable (σ : L →+* L) (τ : B →+* B) [IsLocalHom τ]
  (hστ : (algebraMap B L).comp τ = σ.comp (algebraMap B L))
  (he : S.map τ = nodeTangentSwap S • S) [(S.map (algebraMap B L)).IsElliptic]

/-- The explicit point calculation makes the rational component image fixed. -/
theorem shearedComponentExtension_fixed (h : S = integralRootShear B s • W.map g)
    (hs : σ (s : L) = (s : L) - (S.a₁ : L)) (hf : ∀ x, σ (f x) = f x)
    {π : B} {n : ℕ} (D : SplitNodeDepth S π n) (hπ : τ π = π)
    (c : EllipticComponentQuotient A W) :
    nodeGaloisComponentAction B S σ τ hστ he D hπ
        (shearedComponentExtension B s S A W f g hc h c) =
      shearedComponentExtension B s S A W f g hc h c := by
  obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A W c
  rw [shearedComponentExtension_mk, nodeGaloisComponentAction_mk]
  apply congrArg (ellipticComponentHom B S)
  subst S
  exact nodeGaloisPointAction_fixed_shear_extension B (W.map g) s σ τ hστ he hs
    (W.map (algebraMap A K)) f hf (by rw [map_map, map_map, hc]) P

end FLT.Mazur

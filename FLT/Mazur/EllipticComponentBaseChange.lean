/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticReductionBaseChange
public import FLT.Mazur.EllipticComponentQuotient

/-!
# Injectivity of the rational component comparison

For compatible field and local valuation-ring maps, extending actual rational
points induces an injective homomorphism on E/E₀. The kernel calculation uses
the proved reflection of smooth reduction, not an assumed component comparison.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {K L : Type*} [Field K] [Field L]
  (A : ValuationSubring K) (B : ValuationSubring L) (W : WeierstrassCurve A)
  (f : K →+* L) (g : A →+* B) [IsLocalHom g]
  (hc : (algebraMap B L).comp g = f.comp (algebraMap A K))

/-- Base change of rational points descends to the actual component quotients. -/
noncomputable def integralComponentExtension :
    EllipticComponentQuotient A W →+ EllipticComponentQuotient B (W.map g) :=
  QuotientAddGroup.map (ellipticE0 A W) (ellipticE0 B (W.map g))
    (integralProjectiveExtension A B W f g hc) (fun P hP =>
      (smoothReduction_integralProjectiveExtension A B W f g hc P).mpr hP)

/-- Component base change sends the class of a rational point to its extended class. -/
theorem integralComponentExtension_mk (P : (W.map (algebraMap A K)).toProjective.Point) :
    integralComponentExtension A B W f g hc (ellipticComponentHom A W P) =
      ellipticComponentHom B (W.map g) (integralProjectiveExtension A B W f g hc P) := rfl

/-- A component class becomes zero after extension exactly when it was already zero. -/
theorem integralComponentExtension_eq_zero (c : EllipticComponentQuotient A W) :
    integralComponentExtension A B W f g hc c = 0 ↔ c = 0 := by
  obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A W c
  rw [integralComponentExtension_mk, ellipticComponentHom_eq_zero, ellipticComponentHom_eq_zero]
  exact smoothReduction_integralProjectiveExtension A B W f g hc P

/-- The comparison of actual rational component quotients is injective. -/
theorem integralComponentExtension_injective :
    Function.Injective (integralComponentExtension A B W f g hc) :=
  (injective_iff_map_eq_zero _).mpr fun c => (integralComponentExtension_eq_zero A B W f g hc c).mp

end FLT.Mazur

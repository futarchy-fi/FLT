/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationQcqsBoundaryNumerator
public import FLT.Mazur.IdealSheafClosedTransitions

/-!
# Exact ideal-boundary numerators on named principal domains

The boundary hypothesis is stated on the full pulled ideal subscheme of the
named domain. Its Cartesian square transports the equation to principal
boundary coordinates, where qcqs denominator clearing constructs the global
invariant numerator with the exact full boundary value.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeRelationQcqsBoundaryNumerator
open SchemeEffectiveEpiSections InvariantOpenCoefficientRestriction
open SchemeFiniteGroupQuotient IdealSheafClosedTransitions
set_option backward.isDefEq.respectTransparency false
variable {D X : Scheme.{0}} (p q : D ⟶ X) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace D] [QuasiSeparatedSpace D] (r : compatibleFunctions p q)
  (I : X.IdealSheafData) [CompactSpace I.subscheme] [QuasiSeparatedSpace I.subscheme]
  (U : X.Opens) (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U) (hUr : U = X.basicOpen r.val)

include hUr in
/-- A local full ideal-boundary equation yields an exact global invariant scalar multiple. -/
theorem exists_ideal_boundary_numerator (v : coefficients p q U hU)
    (t : Γ(I.subscheme, ⊤))
    (hv : (I.comap U.ι).subschemeι.appTop v.val =
      (map (I.comap U.ι) I U.ι rfl).appTop t) :
    ∃ (n : ℕ) (w : compatibleFunctions p q),
      I.subschemeι.appTop w.val = (I.subschemeι.appTop r.val) ^ n * t ∧
      U.ι.appTop w.val = (U.ι.appTop r.val) ^ n * v.val := by
  subst U
  let V := X.basicOpen r.val
  let W := I.subscheme.basicOpen (I.subschemeι.appTop r.val)
  let H := isPullback (I.comap V.ι) I V.ι rfl
  let f := principalPullbackMap I.subschemeι r.val
  let g := H.lift f W.ι (principalPullbackMap_inclusion I.subschemeι r.val)
  have h₁ : g ≫ (I.comap V.ι).subschemeι = f := H.lift_fst _ _ _
  have h₂ : g ≫ map (I.comap V.ι) I V.ι rfl = W.ι := H.lift_snd _ _ _
  apply exists_boundary_numerator p q r I.subschemeι v t
  have he := congrArg g.appTop hv
  change (g ≫ (I.comap V.ι).subschemeι).appTop v.val =
    (g ≫ map (I.comap V.ι) I V.ι rfl).appTop t at he
  rwa [h₁, h₂] at he

include hUr in
/-- Homogeneous corrections extend to the entire source with zero on its full boundary. -/
theorem exists_ideal_kernel_numerator (v : coefficients p q U hU)
    (hv : (I.comap U.ι).subschemeι.appTop v.val = 0) :
    ∃ (n : ℕ) (w : compatibleFunctions p q), I.subschemeι.appTop w.val = 0 ∧
      U.ι.appTop w.val = (U.ι.appTop r.val) ^ n * v.val := by
  obtain ⟨n, w, hw, he⟩ := exists_ideal_boundary_numerator p q r I U hU hUr v 0
    (by simpa only [map_zero] using hv)
  exact ⟨n, w, by simpa only [mul_zero] using hw, he⟩

end FLT.Mazur.SchemeRelationQcqsBoundaryNumerator

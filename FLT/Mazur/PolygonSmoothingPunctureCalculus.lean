/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingNilpotentPunctureEquiv
public import FLT.Mazur.PolygonSmoothingParameterEquiv

/-!
# Full puncture calculus for composition, reflection, and inversion

The Boolean label selects the original coordinate: true is left and false is
right. Reflection interchanges these labels without discarding either arrow.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
variable {R : Type*} [CommRing R]
set_option backward.isDefEq.respectTransparency false

/-- Restrict to either original coordinate puncture, using that coordinate as T. -/
def punctureLaurentMap (t : R) : Bool → ChartRing t →ₐ[R] R[T;T⁻¹]
  | true => leftLaurentMap t
  | false => (leftLaurentMap t).comp (branchSwapMap t)

/-- Reflection exchanges the two complete punctures. -/
theorem punctureLaurentMap_swap (t : R) (b : Bool) :
    (punctureLaurentMap t b).comp (branchSwapMap t) = punctureLaurentMap t (!b) := by
  cases b
  · change ((leftLaurentMap t).comp (branchSwapMap t)).comp (branchSwapMap t) = _
    rw [AlgHom.comp_assoc, branchSwapMap_comp, AlgHom.comp_id]
    rfl
  · rfl

/-- Equal-parameter identification preserves each complete puncture. -/
theorem punctureLaurentMap_parameter (s t : R) (h : s = t) (b : Bool) :
    (punctureLaurentMap t b).comp (nodeParameterEquiv s t h).toAlgHom =
      punctureLaurentMap s b := by
  subst t
  rfl

/-- Full puncture factorizations compose in their actual ring-map order. -/
theorem punctureFactor_comp (r s t : R)
    (f : ChartRing s →ₐ[R] ChartRing t) (g : ChartRing r →ₐ[R] ChartRing s)
    (a d : R[T;T⁻¹] →ₐ[R] R[T;T⁻¹]) (b : Bool)
    (hf : (punctureLaurentMap t b).comp f = a.comp (punctureLaurentMap s b))
    (hg : (punctureLaurentMap s b).comp g = d.comp (punctureLaurentMap r b)) :
    (punctureLaurentMap t b).comp (f.comp g) =
      (a.comp d).comp (punctureLaurentMap r b) := by
  rw [← AlgHom.comp_assoc, hf, AlgHom.comp_assoc, hg, ← AlgHom.comp_assoc]

/-- Reflecting the full node factor uses the opposite puncture substitution. -/
theorem punctureFactor_reflect (s t : R) (f : ChartRing s →ₐ[R] ChartRing t)
    (a : Bool → R[T;T⁻¹] →ₐ[R] R[T;T⁻¹])
    (hf : ∀ b, (punctureLaurentMap t b).comp f = (a b).comp (punctureLaurentMap s b))
    (b : Bool) :
    (punctureLaurentMap t b).comp ((branchSwapMap t).comp (f.comp (branchSwapMap s))) =
      (a (!b)).comp (punctureLaurentMap s b) := by
  rw [← AlgHom.comp_assoc, punctureLaurentMap_swap, ← AlgHom.comp_assoc,
    hf, AlgHom.comp_assoc, punctureLaurentMap_swap, Bool.not_not]

/-- Inverting a whole-node equivalence inverts its complete puncture equivalence. -/
theorem punctureFactor_symm (s t : R) (f : ChartRing s ≃ₐ[R] ChartRing t)
    (a : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹]) (b : Bool)
    (hf : (punctureLaurentMap t b).comp f.toAlgHom =
      a.toAlgHom.comp (punctureLaurentMap s b)) :
    (punctureLaurentMap s b).comp f.symm.toAlgHom =
      a.symm.toAlgHom.comp (punctureLaurentMap t b) := by
  apply AlgHom.ext
  intro x
  apply a.injective
  have h := AlgHom.congr_fun hf (f.symm x)
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply] using h.symm

/-- The exact shear substitution on the selected coordinate puncture. -/
def nilpotentShearPunctureEquiv (t e : R) (he : IsNilpotent e) (c : R)
    (p : ChartRing t) : Bool → R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹]
  | true => nilpotentShearLeftEquiv t e he p
  | false => nilpotentShearRightEquiv t e he c p

/-- Both full punctures of the actual node shear factor through their constructed equivalences. -/
theorem nilpotentShear_puncture (t e : R) (he : IsNilpotent e) (c : R)
    (p : ChartRing t) (b : Bool) :
    (punctureLaurentMap t b).comp (nilpotentShearEquiv t e he c p).toAlgHom =
      (nilpotentShearPunctureEquiv t e he c p b).toAlgHom.comp
        (punctureLaurentMap ((1 + e * c) * t) b) := by
  cases b
  · exact nilpotentShear_right_puncture t e he c p
  · exact nilpotentShear_left_puncture t e he c p

end FLT.Mazur.PolygonSmoothing

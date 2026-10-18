/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingCompatibleLaurentLift
public import FLT.Mazur.PolygonSmoothingPunctureNaturality

/-!
# Detecting a full coefficient square on both punctures

The two original Laurent branches jointly detect every node function. Thus
compatible full puncture substitutions determine the whole coefficient square.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

/-- Both complete punctures jointly detect equality of original node functions. -/
theorem punctureLaurent_ext (t : R) (z w : ChartRing t)
    (h : ∀ b, punctureLaurentMap t b z = punctureLaurentMap t b w) : z = w := by
  apply pairedLaurent_ext t
  · exact h true
  · exact congrArg LaurentPolynomial.invert (h false)

/-- Full compatible punctures force the actual coefficient square on the entire node. -/
theorem punctureFactor_coefficientSquare (F : R →+* S) (r t : R) (s v : S)
    (hr : F r = s) (ht : F t = v)
    (f : ChartRing r ≃ₐ[R] ChartRing t) (g : ChartRing s ≃ₐ[S] ChartRing v)
    (a : Bool → R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹])
    (d : Bool → S[T;T⁻¹] ≃ₐ[S] S[T;T⁻¹])
    (hf : ∀ b, (punctureLaurentMap t b).comp f.toAlgHom =
      (a b).toAlgHom.comp (punctureLaurentMap r b))
    (hg : ∀ b, (punctureLaurentMap v b).comp g.toAlgHom =
      (d b).toAlgHom.comp (punctureLaurentMap s b))
    (ha : ∀ b, (coeffMap F).comp (a b).toRingHom =
      (d b).toRingHom.comp (coeffMap F)) :
    (ringMap F t v ht).comp f.toRingHom =
      g.toRingHom.comp (ringMap F r s hr) := by
  apply RingHom.ext
  intro x
  apply punctureLaurent_ext v
  intro b
  have ht' := DFunLike.congr_fun (ringMap_punctureLaurent F t v ht b) (f x)
  have hr' := DFunLike.congr_fun (ringMap_punctureLaurent F r s hr b) x
  have hf' := AlgHom.congr_fun (hf b) x
  have hg' := AlgHom.congr_fun (hg b) (ringMap F r s hr x)
  have ha' := DFunLike.congr_fun (ha b) (punctureLaurentMap r b x)
  change punctureLaurentMap v b (ringMap F t v ht (f x)) =
    punctureLaurentMap v b (g (ringMap F r s hr x))
  change punctureLaurentMap v b (ringMap F t v ht (f x)) =
    coeffMap F (punctureLaurentMap t b (f x)) at ht'
  change punctureLaurentMap s b (ringMap F r s hr x) =
    coeffMap F (punctureLaurentMap r b x) at hr'
  change punctureLaurentMap t b (f x) = a b (punctureLaurentMap r b x) at hf'
  change punctureLaurentMap v b (g (ringMap F r s hr x)) =
    d b (punctureLaurentMap s b (ringMap F r s hr x)) at hg'
  change coeffMap F (a b (punctureLaurentMap r b x)) =
    d b (coeffMap F (punctureLaurentMap r b x)) at ha'
  rw [ht', hf', ha', hg', hr']

end FLT.Mazur.PolygonSmoothing

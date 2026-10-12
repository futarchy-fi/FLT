/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearLineBoundary

/-!
# The algebra map of the whole original punctured tangent line

Localize the actual line contraction at its original horizontal function.
Its spectrum is the canonical lift defining the full scheme intersection.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S s = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (v : S) (hv : v * (v + (WeierstrassDividedDepth.rootShearCurve
    (W.map (algebraMap R S)) r).a₁) = 0)
local notation "T₀" => ScalarExtension W s π b3 b4 b6 S
local notation "u₀" => tensorCoord W s π b3 b4 b6 S 2
local notation "H" => Localization.Away u₀
local notation "l" => tensorShearLineMap W s π b3 b4 b6 S r hs hp h3 h4 hr v hv
local notation "i" => PrincipalOpenTensor.inclusion S (coord W s π b3 b4 b6 2)

/-- Restrict every horizontal localized tensor function to the punctured tangent line. -/
def tensorShearLineOpenMap : H →ₐ[S] S[T;T⁻¹] :=
  IsLocalization.Away.liftAlgHom u₀ (f := Polynomial.toLaurentAlg.comp l) (by
    change IsUnit (Polynomial.toLaurent (l u₀))
    rw [tensorShearLineMap_coord]
    change IsUnit (Polynomial.toLaurent (Polynomial.X : Polynomial S))
    rw [Polynomial.toLaurent_X]
    exact LaurentPolynomial.isUnit_T 1)

/-- All original tensor functions retain their line restrictions. -/
theorem tensorShearLineOpenMap_base (z : T₀) :
    tensorShearLineOpenMap W s π b3 b4 b6 S r hs hp h3 h4 hr v hv (algebraMap T₀ H z) =
      Polynomial.toLaurent (l z) := by
  rw [tensorShearLineOpenMap, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- This explicit localized map is exactly the canonical full-intersection lift. -/
theorem tensorShearLineOpenMap_spec :
    Spec.map (CommRingCat.ofHom
      (tensorShearLineOpenMap W s π b3 b4 b6 S r hs hp h3 h4 hr v hv).toRingHom) =
      tensorShearLineToHorizontal W s π b3 b4 b6 S r hs hp h3 h4 hr v hv := by
  apply (cancel_mono i).mp
  rw [tensorShearLineToHorizontal_comp]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (tensorShearLineOpenMap_base W s π b3 b4 b6 S r hs hp h3 h4 hr v hv)

end FLT.Mazur.WeierstrassSuccessiveX

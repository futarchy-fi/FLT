/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialFactorRatioCoefficient
public import FLT.Mazur.WeierstrassModificationXPolynomialFactorRatioGeometry

/-!
# Scheme coefficient squares for the corrected full node isomorphism

Both directions use the original arithmetic coefficient map and every localized
function, with independently specified normalized target smoothing.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (ha : IsUnit W.a₁) (s τ : R)
  (hτ : s = W.a₁ ^ 2 * τ) (τ' : S) (hτ' : f s = (W.map f).a₁ ^ 2 * τ') (ht : f τ = τ')
  (b3 b4 b6 : R) (r : R[X])
  (hr : r ^ 2 + polynomialSlopeLinear W b3 * r = polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)
  (hI : IsNilpotent I) (hJ : IsNilpotent J) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "U" => W.map f
local notation "hrJ" => polynomialArithmeticIdeal_coefficient f I J hf hrI
local notation "hr'" => polynomialRootEquation_coefficient f W b3 b4 b6 r hr
local notation "E" => polynomialFactorRatioIso W ha s τ hτ b3 b4 b6 r hr I hI hrI h3
local notation "E'" => polynomialFactorRatioIso U (ha.map f) (f s) τ' hτ'
  (f b3) (f b4) (f b6) (r.map f) hr' J hJ hrJ (hf h3)
local notation "g" => nodeOpenCoefficientRingMap f W s
local notation "d" => NodalFiber.tangentCoefficientRingMap f τ (-1 : R) τ' (-1 : S) ht (by simp)

/-- The corrected full node isomorphism commutes with the actual original coefficient morphism. -/
@[reassoc] theorem polynomialFactorRatioIso_hom_coefficient :
    Spec.map (CommRingCat.ofHom g) ≫ (E).hom =
      (E').hom ≫ Spec.map (CommRingCat.ofHom d) := by
  rw [polynomialFactorRatioIso_hom, polynomialFactorRatioIso_hom]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun k ↦ Spec.map (CommRingCat.ofHom k))
    (polynomialFactorRatioMap_coefficient f W ha s τ hτ τ' hτ' ht
      b3 b4 b6 r hr I J hf hI hJ hrI h3)

/-- The full inverse isomorphism has the reverse original coefficient square. -/
@[reassoc] theorem polynomialFactorRatioIso_inv_coefficient :
    Spec.map (CommRingCat.ofHom d) ≫ (E).inv =
      (E').inv ≫ Spec.map (CommRingCat.ofHom g) := by
  apply (cancel_mono (E).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [polynomialFactorRatioIso_hom_coefficient f W ha s τ hτ τ' hτ' ht
    b3 b4 b6 r hr I J hf hI hJ hrI h3, Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassModificationX

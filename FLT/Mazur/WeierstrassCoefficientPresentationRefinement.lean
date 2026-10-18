/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassCoefficientModelComposition

/-!
# Coefficient towers with named composite homomorphisms

The full model coherence allows a separately extracted coefficient map on
the refined chart. Its equality with the composite is carried by base change.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
open GeneralizedEllipticCurve
set_option backward.isDefEq.respectTransparency false
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
  (W : WeierstrassCurve R) (V : WeierstrassCurve A) (Z : WeierstrassCurve B)
  (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) (hZ : IsUnit Z.Δ)
  (f : R →+* A) (g : A →+* B) (j : R →+* B) (hj : j = g.comp f)
  (hf : V = W.map f) (hg : Z = V.map g) (hgf : Z = W.map j)
local notation "E" => integralGeneralizedEllipticCurve W hW
local notation "kf" => Spec.map (CommRingCat.ofHom f)
local notation "kg" => Spec.map (CommRingCat.ofHom g)
local notation "kj" => Spec.map (CommRingCat.ofHom j)

/-- Named composite coefficient maps retain the exact full model refinement square. -/
theorem coefficientPresentationIso_refine :
    (coefficientPresentationIso W hW j Z hZ hgf).hom ≫
      ((E).baseChangeCompEqIso kf kg kj
        ((congrArg (fun t ↦ Spec.map (CommRingCat.ofHom t)) hj).trans
          (Spec.map_comp _ _))).hom =
    (coefficientPresentationIso V hV g Z hZ hg).hom ≫
      baseChangeMap kg (coefficientPresentationIso W hW f V hV hf).hom := by
  subst j
  exact coefficientPresentationIso_comp W V Z hW hV hZ f g hf hg hgf

end FLT.Mazur.WeierstrassIntegralChart

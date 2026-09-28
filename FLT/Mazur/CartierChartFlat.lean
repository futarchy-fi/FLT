/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierCharts

/-!
# Flat quotients on Cartier charts

The quotient comparison on an affine chart respects the map from the base.
Consequently, flatness of the divisor over the base gives flatness of the
displayed composite into the quotient by the chart equation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {X S : Scheme.{u}}

private lemma quotient_mk_eqToIso {R : Type u} [CommRing R] (J K : Ideal R)
    (h : J = K) :
    CommRingCat.ofHom (Ideal.Quotient.mk J) ≫
        (eqToIso (show CommRingCat.of (R ⧸ J) = CommRingCat.of (R ⧸ K) by rw [h])).hom =
      CommRingCat.ofHom (Ideal.Quotient.mk K) := by
  subst K
  rfl

/-- The chart comparison carries restriction to the canonical quotient map. -/
@[reassoc (attr := simp)]
lemma subschemeι_app_cartierChartQuotientIso_hom (I : X.IdealSheafData)
    (U : X.affineOpens) (h : Γ(X, U)) (hh : I.ideal U = Ideal.span {h}) :
    I.subschemeι.app U ≫ (cartierChartQuotientIso I U h hh).hom =
      CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {h})) := by
  rw [I.subschemeι_app U]
  simp only [cartierChartQuotientIso, Iso.trans_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  exact quotient_mk_eqToIso _ _ hh

/-- The quotient's structure map is the given base map followed by the quotient map. -/
lemma cartierChartQuotientIso_baseMap (f : X ⟶ S) (I : X.IdealSheafData)
    (V : S.affineOpens) (U : X.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1)
    (h : Γ(X, U)) (hh : I.ideal U = Ideal.span {h}) :
    (I.subschemeι ≫ f).appLE V (I.subschemeι ⁻¹ᵁ U)
        (fun _ hx ↦ e hx) ≫ (cartierChartQuotientIso I U h hh).hom =
      f.appLE V U e ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {h})) := by
  rw [← Scheme.Hom.appLE_comp_appLE I.subschemeι f V U
    (I.subschemeι ⁻¹ᵁ U) e le_rfl]
  rw [← Scheme.Hom.app_eq_appLE]
  rw [Category.assoc, subschemeι_app_cartierChartQuotientIso_hom]

/-- A divisor flat over the base has a flat quotient on each principal affine chart. -/
theorem flat_cartierChart_quotient (f : X ⟶ S) (I : X.IdealSheafData)
    [Flat (I.subschemeι ≫ f)] (V : S.affineOpens) (U : X.affineOpens)
    (e : U.1 ≤ f ⁻¹ᵁ V.1) (h : Γ(X, U)) (hh : I.ideal U = Ideal.span {h}) :
    ((Ideal.Quotient.mk (Ideal.span {h})).comp (f.appLE V U e).hom).Flat := by
  have hf := (I.subschemeι ≫ f).flat_appLE V.2 (U.2.preimage I.subschemeι)
    (show I.subschemeι ⁻¹ᵁ U.1 ≤ (I.subschemeι ≫ f) ⁻¹ᵁ V.1 from fun _ hx ↦ e hx)
  have he := RingHom.Flat.comp hf
    (RingHom.Flat.of_bijective
      (cartierChartQuotientIso I U h hh).commRingCatIsoToRingEquiv.bijective)
  change (((I.subschemeι ≫ f).appLE V (I.subschemeι ⁻¹ᵁ U)
    (fun _ hx ↦ e hx) ≫ (cartierChartQuotientIso I U h hh).hom).hom).Flat at he
  rwa [cartierChartQuotientIso_baseMap] at he

end FLT.Mazur.FCurve

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSlopeLaurent
public import FLT.Mazur.WeierstrassDividedZeroExteriorCurve
public import FLT.Mazur.WeierstrassSlopeLaurentGeometry

/-!
# The retained start-zero exterior in its original Laurent coordinates

The retained original attachment is precisely the canonical ordered tangent
ratio. Its full infinity image is T-1, and the exterior curve is the actual
pushout of the complete slope affine line and Laurent torus along this map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassModificationX WeierstrassIntegralChart
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "u" => Units.mk0 a (IsUnit.ne_zero (D.a₁_unit.map (residue R)))
local notation "s" => PrincipalOpenTransport.inclusion (slopePolynomial a)
local notation "t" => olderGlobalZeroSlopeToInfinity hπ data D j hj r hr hk0 hk
local notation "e" => infinityResidueIso D (by omega : 0 < depth)
local notation "m" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (slopeLaurentMap u)))
local notation "l" => zeroRetainedExteriorAffineChart hπ data D j hj r hr hk0 hk
local notation "ic" => zeroRetainedExteriorInfinityChart hπ data D j hj r hr hk0 hk

/-- The whole original Laurent infinity chart embeds in the actual exterior curve. -/
def zeroRetainedExteriorLaurentChart : Spec (.of K[T;T⁻¹]) ⟶
    zeroRetainedExteriorCurve hπ data D j hj r hr hk0 hk := (e).hom ≫ ic

instance zeroRetainedExteriorLaurentChart_isOpenImmersion :
    IsOpenImmersion (zeroRetainedExteriorLaurentChart hπ data D j hj r hr hk0 hk) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The complete original exterior gluing is the canonical slope/Laurent pushout. -/
theorem zeroRetainedExteriorLaurent_isPushout :
    IsPushout s m l (zeroRetainedExteriorLaurentChart hπ data D j hj r hr hk0 hk) := by
  apply (IsPushout.of_hasPushout s t).of_iso'
    (Iso.refl _) (Iso.refl _) e (Iso.refl _)
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp]
    rw [← zeroRetainedSlopeToInfinity_canonical hπ data D j hj r hr hk0 hk,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl

/-- The canonical gluing identifies the actual original exterior scheme. -/
def zeroRetainedExteriorLaurentGluingIso : pushout s m ≅
    zeroRetainedExteriorCurve hπ data D j hj r hr hk0 hk :=
  (zeroRetainedExteriorLaurent_isPushout hπ data D j hj r hr hk0 hk).isoPushout.symm

/-- The comparison retains the full incidence line and both original node markings. -/
@[reassoc] theorem zeroRetainedExteriorLaurentGluingIso_affine :
    pushout.inl s m ≫ (zeroRetainedExteriorLaurentGluingIso hπ data D j hj r hr hk0 hk).hom =
      l := (zeroRetainedExteriorLaurent_isPushout hπ data D j hj r hr hk0 hk).inl_isoPushout_inv

/-- The comparison retains the entire original normalized infinity chart. -/
@[reassoc] theorem zeroRetainedExteriorLaurentGluingIso_infinity :
    pushout.inr s m ≫ (zeroRetainedExteriorLaurentGluingIso hπ data D j hj r hr hk0 hk).hom =
      zeroRetainedExteriorLaurentChart hπ data D j hj r hr hk0 hk :=
  (zeroRetainedExteriorLaurent_isPushout hπ data D j hj r hr hk0 hk).inr_isoPushout_inv

/-- The full Laurent chart retains the original residue coefficient structure. -/
@[reassoc] theorem zeroRetainedExteriorLaurentChart_structure :
    zeroRetainedExteriorLaurentChart hπ data D j hj r hr hk0 hk ≫
      zeroRetainedExteriorStructure hπ data D j hj r hr hk0 hk =
        (MultiplicativeGroupScheme.gm K).hom := by
  rw [zeroRetainedExteriorLaurentChart, Category.assoc, zeroRetainedExteriorStructure_infinity]
  exact infinityResidueIso_structure D (by omega)

end FLT.Mazur.WeierstrassDividedDepth

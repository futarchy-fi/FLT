/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialSlopeTransition
public import FLT.Mazur.WeierstrassDividedInitialExteriorCurve
public import FLT.Mazur.WeierstrassSlopeLaurentGeometry

/-!
# The actual exterior gluing in canonical Laurent coordinates

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
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hstart : 0 < start) (hk : 2 * start ≤ depth) (hdepth : 0 < depth)
open WeierstrassModificationX WeierstrassIntegralChart
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "u" => Units.mk0 a (IsUnit.ne_zero (residue_tangent_isUnit D))
local notation "s" => PrincipalOpenTransport.inclusion (slopePolynomial a)
local notation "t" => initialGlobalSlopeToInfinity hπ data D j hj hstart hk
local notation "e" => infinityResidueIso D hdepth
local notation "m" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (slopeLaurentMap u)))
local notation "l" => initialExteriorAffineChart hπ data D j hj hstart hk
local notation "r" => initialExteriorInfinityChart hπ data D j hj hstart hk

/-- The actual original attachment has the canonical ordered tangent ratio on all functions. -/
theorem initialGlobalSlopeToInfinity_canonical : t ≫ (e).inv = m := by
  rw [initialGlobalSlopeToInfinity_laurent]
  congr 1
  apply CommRingCat.hom_ext
  apply congrArg AlgHom.toRingHom
  apply slopeLaurent_hom_ext
  rw [residueSlopeLaurentMap_T]
  exact (slopeLaurentMap_T u).symm

/-- The full actual incidence/infinity intersection is the Laurent torus punctured at one. -/
theorem initialGlobalSlopeToInfinity_laurent_range :
    Set.range (t ≫ (e).inv) =
      (PrimeSpectrum.basicOpen (LaurentPolynomial.T 1 - 1 : K[T;T⁻¹]) :
        Set (PrimeSpectrum K[T;T⁻¹])) := by
  rw [initialGlobalSlopeToInfinity_canonical]
  exact slopeLaurentMap_range u

/-- The whole original Laurent infinity chart embeds in the actual exterior curve. -/
def initialExteriorLaurentChart : Spec (.of K[T;T⁻¹]) ⟶
    initialExteriorCurve hπ data D j hj hstart hk := (e).hom ≫ r

instance initialExteriorLaurentChart_isOpenImmersion :
    IsOpenImmersion (initialExteriorLaurentChart hπ data D j hj hstart hk hdepth) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The complete original exterior gluing is the canonical slope/Laurent pushout. -/
theorem initialExteriorLaurent_isPushout :
    IsPushout s m l (initialExteriorLaurentChart hπ data D j hj hstart hk hdepth) := by
  apply (IsPushout.of_hasPushout s t).of_iso'
    (Iso.refl _) (Iso.refl _) e (Iso.refl _)
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp]
    rw [← initialGlobalSlopeToInfinity_canonical hπ data D j hj hstart hk hdepth,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl

/-- The canonical gluing identifies the actual original exterior scheme. -/
def initialExteriorLaurentGluingIso : pushout s m ≅
    initialExteriorCurve hπ data D j hj hstart hk :=
  (initialExteriorLaurent_isPushout hπ data D j hj hstart hk hdepth).isoPushout.symm

/-- The comparison retains the full incidence line and both original node markings. -/
@[reassoc] theorem initialExteriorLaurentGluingIso_affine :
    pushout.inl s m ≫ (initialExteriorLaurentGluingIso hπ data D j hj hstart hk hdepth).hom =
      l := (initialExteriorLaurent_isPushout hπ data D j hj hstart hk hdepth).inl_isoPushout_inv

/-- The comparison retains the entire original normalized infinity chart. -/
@[reassoc] theorem initialExteriorLaurentGluingIso_infinity :
    pushout.inr s m ≫ (initialExteriorLaurentGluingIso hπ data D j hj hstart hk hdepth).hom =
      initialExteriorLaurentChart hπ data D j hj hstart hk hdepth :=
  (initialExteriorLaurent_isPushout hπ data D j hj hstart hk hdepth).inr_isoPushout_inv

/-- The full Laurent chart retains the original residue coefficient structure. -/
@[reassoc] theorem initialExteriorLaurentChart_structure :
    initialExteriorLaurentChart hπ data D j hj hstart hk hdepth ≫
      initialExteriorStructure hπ data D j hj hstart hk =
        (MultiplicativeGroupScheme.gm K).hom := by
  rw [initialExteriorLaurentChart, Category.assoc, initialExteriorStructure_infinity]
  exact infinityResidueIso_structure D hdepth

end FLT.Mazur.WeierstrassDividedDepth

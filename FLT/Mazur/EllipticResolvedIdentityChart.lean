/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedSmoothPoint
public import FLT.Mazur.WeierstrassInfinityResidueSmooth

/-!
# The original identity torus in the resolved split fiber

The entire original smooth residue cubic embeds in the actual final model.
Its Laurent parametrization retains the original contraction and coefficient
map, and its image is precisely the preimage of the original smooth open.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- The smooth Laurent comparison retains the original coefficient structure. -/
@[reassoc] theorem splitEquationSmoothIso_structure {F : Type u} [CommRing F]
    {U : WeierstrassCurve F} (a : Fˣ) (h : U = splitNodalEquation a) :
    (splitEquationSmoothIso a h).hom ≫ integralSmoothStructure U =
      (MultiplicativeGroupScheme.gm F).hom := by
  subst U
  exact splitNodalRelativeSmoothIso_structure a

/-- The original split residue parametrization is over the original residue field. -/
@[reassoc] theorem infinityResidueSmoothIso_structure
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
    (hd : 0 < depth) :
    (infinityResidueSmoothIso D hd).hom ≫
      integralSmoothStructure (W.map (algebraMap R (ResidueField R))) =
        (MultiplicativeGroupScheme.gm (ResidueField R)).hom :=
  splitEquationSmoothIso_structure _ _

end FLT.Mazur.WeierstrassIntegralChart

namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
local notation "F" => ResidueField A
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A F))
local notation "f" => finiteGlobalStructure hπ data (depth / 2) (le_refl _)
local notation "p" => resolvedSplitStructure A D

/-- The identity torus embeds through the complete original smooth residue cubic. -/
def resolvedIdentityChart : Spec (.of F[T;T⁻¹]) ⟶ resolvedSplitFiber A D :=
  (infinityResidueSmoothIso D D.depth_pos).hom ≫
    finiteGlobalSmoothCoefficientEmbedding F hπ data (depth / 2) (le_refl _)

instance resolvedIdentityChart_isOpenImmersion : IsOpenImmersion (resolvedIdentityChart A D) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The identity torus retains its actual residue-field structure map. -/
@[reassoc] theorem resolvedIdentityChart_structure :
    resolvedIdentityChart A D ≫ p = (MultiplicativeGroupScheme.gm F).hom := by
  rw [resolvedIdentityChart, Category.assoc, resolvedSplitStructure,
    finiteGlobalSmoothCoefficientEmbedding_structure, infinityResidueSmoothIso_structure]

/-- Contraction is the full original infinity Laurent parametrization. -/
@[reassoc] theorem resolvedIdentityChart_contraction :
    resolvedIdentityChart A D ≫ pullback.snd q f ≫
      finiteGlobalContraction hπ data (depth / 2) (le_refl _) =
        infinityResidueContraction D D.depth_pos := by
  rw [resolvedIdentityChart, Category.assoc,
    finiteGlobalSmoothCoefficientEmbedding_contraction, infinityResidueSmoothIso_contraction]

/-- Every point over the original smooth cubic belongs to this identity torus. -/
theorem resolvedIdentityChart_range :
    Set.range (resolvedIdentityChart A D) =
      (pullback.snd q f ≫ finiteGlobalContraction hπ data (depth / 2) (le_refl _)) ⁻¹'
        (integralSmoothOpen W : Set _) := by
  rw [resolvedIdentityChart, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (infinityResidueSmoothIso D D.depth_pos).hom.surjective.range_eq, Set.image_univ,
    finiteGlobalSmoothCoefficientEmbedding_range, finiteGlobalSmoothEmbedding_range]
  rfl

/-- The whole identity torus lies in the actual resolved smooth fiber. -/
theorem resolvedIdentityChart_mem_smooth (z : Spec (.of F[T;T⁻¹])) :
    resolvedIdentityChart A D z ∈ (p).smoothLocus := by
  apply (PolygonAtlas.mem_smooth_iff (resolvedIdentityChart A D) p z).mpr
  have hs : Smooth (resolvedIdentityChart A D ≫ p) := by
    rw [resolvedIdentityChart_structure]
    infer_instance
  rw [Scheme.Hom.smoothLocus_eq_top]
  trivial

/-- The original identity Laurent chart lifted to the actual resolved smooth open. -/
def resolvedIdentitySmoothChart : Spec (.of F[T;T⁻¹]) ⟶ (p).smoothLocus.toScheme :=
  IsOpenImmersion.lift (p).smoothLocus.ι (resolvedIdentityChart A D) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact resolvedIdentityChart_mem_smooth A D z)

instance resolvedIdentitySmoothChart_isOpenImmersion :
    IsOpenImmersion (resolvedIdentitySmoothChart A D) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift _ _ _))

/-- The smooth chart retains the full original resolved-fiber inclusion. -/
@[reassoc] theorem resolvedIdentitySmoothChart_inclusion :
    resolvedIdentitySmoothChart A D ≫ (p).smoothLocus.ι = resolvedIdentityChart A D :=
  IsOpenImmersion.lift_fac _ _ _

end FLT.Mazur.WeierstrassDividedDepth

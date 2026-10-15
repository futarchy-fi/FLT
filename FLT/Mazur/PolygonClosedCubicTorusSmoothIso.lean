/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonClosedCubicSmoothTorus
public import FLT.Mazur.PolygonSmoothFiniteAtlas

/-!
# The full Laurent coordinate on the actual closed cubic smooth locus

Lift the original cubic torus to the smooth locus and prove that it is the
whole smooth cubic. The coordinate still factors the original retained
polygon contraction and preserves the residue-field structure morphism.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completeClosedFiberInclusion completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "c" => Over.hom (closedPointCubicOver K n h i)
local notation "torus" => Spec (CommRingCat.of (LaurentPolynomial K))
local notation "t" => closedPointCubicTorus K n h i

/-- The actual original cubic torus, now valued in its entire smooth locus. -/
def closedPointCubicSmoothTorus : torus ⟶ (c).smoothLocus.toScheme :=
  IsOpenImmersion.lift (c).smoothLocus.ι (t) (by
    rw [Scheme.Opens.range_ι, closedPointCubic_smoothLocus_eq_torus]
    exact fun _ hx => hx)

/-- Smooth lifting retains the original closed cubic Laurent morphism. -/
@[reassoc] theorem closedPointCubicSmoothTorus_inclusion :
    closedPointCubicSmoothTorus K n h i ≫ (c).smoothLocus.ι = t :=
  IsOpenImmersion.lift_fac _ _ _

instance closedPointCubicSmoothTorus_isOpenImmersion :
    IsOpenImmersion (closedPointCubicSmoothTorus K n h i) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift _ _ _))

instance closedPointCubicSmoothTorus_isIso : IsIso (closedPointCubicSmoothTorus K n h i) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply TopologicalSpace.Opens.ext
  apply Set.eq_univ_of_forall
  intro z
  have he := congrArg (fun U : (closedPointCubicOver K n h i).left.Opens => z.1 ∈ U)
    (closedPointCubic_smoothLocus_eq_torus K n h i)
  obtain ⟨x, hx⟩ := he.mp z.2
  refine ⟨x, (c).smoothLocus.ι.isOpenEmbedding.injective ?_⟩
  exact (congrArg (fun f => f x) (closedPointCubicSmoothTorus_inclusion K n h i)).trans hx

/-- The original Laurent parametrization is an isomorphism onto the whole smooth closed cubic. -/
def closedPointCubicSmoothTorusIso : torus ≅ (c).smoothLocus.toScheme :=
  asIso (closedPointCubicSmoothTorus K n h i)

/-- The whole original Laurent parametrization retains its coefficient map. -/
@[reassoc] theorem closedPointCubicSmoothTorus_structure :
    closedPointCubicSmoothTorus K n h i ≫ (c).smoothLocus.ι ≫ c =
      (MultiplicativeGroupScheme.gm K).hom := by
  rw [closedPointCubicSmoothTorus_inclusion_assoc, closedPointCubicTorus, Category.assoc,
    closedPointContractionCubicIso_over]
  exact (PolygonAtlas.torus K 1 0).w

/-- The retained polygon normalization really contracts to this same original torus. -/
@[reassoc] theorem closedPointCubicSmoothTorus_contraction :
    (torusToComponent K ≫ componentι K n i ≫
        PolygonCyclicAtlas.normalization K n h).left ≫ closedPointToCubic K n h i =
      closedPointCubicSmoothTorus K n h i ≫ (c).smoothLocus.ι := by
  rw [closedPointCubicSmoothTorus_inclusion]
  simpa only [Category.id_comp] using (closedPointCubicTorus_isPullback K n h i).w.symm

end FLT.Mazur.PolygonInfinitesimalStages

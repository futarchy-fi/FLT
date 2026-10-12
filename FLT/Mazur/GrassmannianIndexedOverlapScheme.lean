/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientChartIndex
public import FLT.Mazur.GrassmannianAmbientIdentity
public import FLT.Mazur.GrassmannianOverlapTransitionScheme

/-!
# The indexed scheme overlaps and their self-gluing laws

Every ambient decomposition has its affine matrix chart. Between any two indices
we use the actual determinant localization and its constructed reverse isomorphism.
The diagonal overlap inclusion is an isomorphism and its transition is the identity.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M ι : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] {d : ℕ}

/-- The affine chart attached to each ambient decomposition. -/
abbrev indexedChartScheme (_ : AmbientChartIndex R M ι d) := splitChartScheme R ι d

/-- The actual determinant overlap in the first of two indexed charts. -/
abbrev indexedOverlapScheme (i j : AmbientChartIndex R M ι d) :=
  ambientOverlapScheme (ambientChartChange i j)

/-- The principal open embedding into the first indexed chart. -/
def indexedOverlapInclusion (i j : AmbientChartIndex R M ι d) :
    indexedOverlapScheme i j ⟶ indexedChartScheme i :=
  principalOverlapInclusion (ambientBlockP (ambientChartChange i j).toLinearMap)
    (ambientBlockQ (ambientChartChange i j).toLinearMap)

instance (i j : AmbientChartIndex R M ι d) :
    IsOpenImmersion (indexedOverlapInclusion i j) :=
  inferInstanceAs (IsOpenImmersion (principalOverlapInclusion _ _))

/-- The actual scheme transition to the reverse indexed overlap. -/
def indexedOverlapIso (i j : AmbientChartIndex R M ι d) :
    indexedOverlapScheme i j ≅ indexedOverlapScheme j i :=
  ambientOverlapSchemeIso (ambientChartChange i j)

/-- The forward transition into the whole second chart. -/
def indexedChartTransition (i j : AmbientChartIndex R M ι d) :
    indexedOverlapScheme i j ⟶ indexedChartScheme j :=
  localizedChartTransitionScheme (ambientBlockP (ambientChartChange i j).toLinearMap)
    (ambientBlockQ (ambientChartChange i j).toLinearMap)
    (ambientBlockU (ambientChartChange i j).toLinearMap)
    (ambientBlockT (ambientChartChange i j).toLinearMap)

/-- The indexed overlap isomorphism factors the rational transition into the second chart. -/
@[reassoc] theorem indexedOverlapIso_factor (i j : AmbientChartIndex R M ι d) :
    (indexedOverlapIso i j).hom ≫ indexedOverlapInclusion j i = indexedChartTransition i j :=
  ambientOverlapSchemeIso_factor (ambientChartChange i j)

/-- Exchanging chart indices exchanges the two directions of the isomorphism. -/
theorem indexedOverlapIso_symm (i j : AmbientChartIndex R M ι d) :
    (indexedOverlapIso i j).symm = indexedOverlapIso j i := by
  apply Iso.ext
  rfl

/-- The diagonal determinant overlap is the whole original chart. -/
instance indexedOverlapInclusion_self_isIso (i : AmbientChartIndex R M ι d) :
    IsIso (indexedOverlapInclusion i i) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  change (principalOverlapInclusion _ _).opensRange = ⊤
  rw [principalOverlapInclusion_range]
  change (PrimeSpectrum.basicOpen _ :
    TopologicalSpace.Opens (PrimeSpectrum (MvPolynomial (Fin d × ι) R))) = ⊤
  have hp : overlapPolynomial (ambientBlockP (ambientChartChange i i).toLinearMap)
      (ambientBlockQ (ambientChartChange i i).toLinearMap) = 1 := by
    rw [ambientChartChange_self]
    exact ambientOverlapPolynomial_refl
  rw [hp, PrimeSpectrum.basicOpen_one]

/-- The rational diagonal transition equals the original principal open inclusion. -/
theorem indexedChartTransition_self (i : AmbientChartIndex R M ι d) :
    indexedChartTransition i i = indexedOverlapInclusion i i := by
  have h (e : ((Fin d → R) × (ι → R)) ≃ₗ[R] ((Fin d → R) × (ι → R)))
      (he : e = LinearEquiv.refl R _) :
      ambientTransitionPolynomialHom e = Algebra.algHom R _ _ := by
    subst e
    exact ambientTransitionPolynomialHom_refl
  change Spec.map _ = Spec.map _
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (h _ (ambientChartChange_self i))

/-- The actual self-overlap transition is the identity, as required for scheme gluing. -/
theorem indexedOverlapIso_self (i : AmbientChartIndex R M ι d) :
    (indexedOverlapIso i i).hom = 𝟙 _ := by
  apply (cancel_mono (indexedOverlapInclusion i i)).mp
  rw [indexedOverlapIso_factor, indexedChartTransition_self, Category.id_comp]

/-- All indexed overlap identifications preserve the original base scheme. -/
theorem indexedChartTransition_over (i j : AmbientChartIndex R M ι d) :
    indexedChartTransition i j ≫ splitChartStructure R ι d =
      indexedOverlapInclusion i j ≫ splitChartStructure R ι d := by
  exact (localizedChartTransitionScheme_over _ _ _ _).trans
    (principalOverlapInclusion_over _ _).symm

end FLT.Mazur.GrassmannianChart

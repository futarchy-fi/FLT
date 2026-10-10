/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenTransport
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Actual principal-open charts from coordinate equivalences

An equivalence of a principal localization gives an open chart with exactly
the original principal-open image and the original coefficient structure.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.PrincipalOpenTransport
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (x : A) (e : Localization.Away x ≃ₐ[R] B)

/-- The original principal localization inclusion. -/
def inclusion : Spec (.of (Localization.Away x)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x)))

instance inclusion_isOpenImmersion : IsOpenImmersion (inclusion x) :=
  IsOpenImmersion.of_isLocalization x

/-- The actual spectrum isomorphism associated with the coordinate comparison. -/
def chartIso : Spec (.of B) ≅ Spec (.of (Localization.Away x)) :=
  Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op

/-- The chart retains the inclusion of the original principal open. -/
def chart : Spec (.of B) ⟶ Spec (.of A) := (chartIso x e).hom ≫ inclusion x

instance chart_isOpenImmersion : IsOpenImmersion (chart x e) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- Its image is exactly the original principal open, not a smaller neighborhood. -/
theorem chart_range : Set.range (chart x e) =
    (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum A)) := by
  have h : Set.range (chart x e) = Set.range (inclusion x) := by
    change Set.range (fun z ↦ inclusion x ((chartIso x e).hom z)) = _
    simpa only [Function.comp_def, Scheme.Hom.homeomorph_apply] using
      (chartIso x e).hom.homeomorph.surjective.range_comp (inclusion x)
  rw [h]
  exact PrimeSpectrum.localization_away_comap_range _ x

/-- The full chart retains the original structure map to the coefficient spectrum. -/
@[reassoc] theorem chart_structure :
    chart x e ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  change e (algebraMap A (Localization.Away x) (algebraMap R A r)) = algebraMap R B r
  rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]

end FLT.Mazur.PrincipalOpenTransport

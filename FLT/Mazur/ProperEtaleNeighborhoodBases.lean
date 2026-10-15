/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperNeighborhoodAtlas
public import FLT.Mazur.AffineEtaleTranslationNormCharts
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finite etale charts and local bases from proper neighborhoods

Every member of the canonical proper-neighborhood atlas of an etale map is
finite etale over its unchanged ground. Over an affine integer-finite-type
base, its actual section algebra has constructed principal finite-free charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Module TensorProduct
namespace FLT.Mazur.ProperNeighborhoodAtlas
open Approximation
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (i : Index f)

/-- Every proper neighborhood retains the original etale structural morphism. -/
instance projection_etale : Etale (inclusion f i ≫ f) := inferInstance

/-- Etaleness gives quasi-finiteness of the actual proper-neighborhood projection. -/
theorem projection_locallyQuasiFinite : LocallyQuasiFinite (inclusion f i ≫ f) := by
  constructor
  intro U hU W hW h
  have hφ := (inclusion f i ≫ f).etale_appLE hU hW h
  algebraize [((inclusion f i ≫ f).appLE U W h).hom]
  exact inferInstanceAs (Algebra.QuasiFinite _ _)

/-- Zariski's main theorem makes these constructed proper etale charts finite. -/
theorem projection_isFinite : IsFinite (inclusion f i ≫ f) := by
  let _ := projection_locallyQuasiFinite f i
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- Every such chart is affine when its unchanged target is affine. -/
theorem source_isAffine [IsAffine Y] : IsAffine (source f i) := by
  let _ := projection_isFinite f i
  exact isAffine_of_isAffineHom (inclusion f i ≫ f)

variable {R : Type u} [CommRing R] [Algebra.FiniteType ℤ R]
  {V : Scheme.{u}} (g : V ⟶ Spec (.of R)) [Etale g]
  (j : Index g)

/-- The canonical chart has an actual finite section basis after a constructed base localization. -/
theorem exists_principal_section_basis (p : PrimeSpectrum R) :
    let _ := affineBaseSectionAlgebra (inclusion g j ≫ g)
    ∃ r : R, r ∉ p.asIdeal ∧ ∃ n : ℕ,
      Nonempty (Basis (Fin n) (Localization.Away r)
        (Localization.Away r ⊗[R] Γ(source g j, ⊤))) := by
  let _ := projection_isFinite g j
  let _ := source_isAffine g j
  exact EtaleTranslationBranch.exists_section_principal_basis (inclusion g j ≫ g) p

end FLT.Mazur.ProperNeighborhoodAtlas

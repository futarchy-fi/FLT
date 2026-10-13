/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEtaleTranslationFiniteBranch
public import FLT.Mazur.FiniteFlatTranslationNormCharts

/-!
# Local norm bases for actual finite etale translation schemes

Apply the finite-free construction to the original translation section ring,
with its original structural algebra. Finite type over the integers supplies
noetherianity. These bases can be used on the finite faithful refinements of
the Hilbert charts; no global coaction on an affine source is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Module TensorProduct
namespace FLT.Mazur.EtaleTranslationBranch
open Approximation FiniteFreeTranslationNorm
universe u
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] {V : Scheme.{u}}
  (g : V ⟶ Spec (.of R)) [IsAffine V]

/-- A finite affine translation has a finite original section algebra. -/
theorem sectionAlgebra_finite [IsFinite g] :
    let _ := affineBaseSectionAlgebra g
    Module.Finite R Γ(V, ⊤) := by
  let _ := affineBaseSectionAlgebra g
  let _ : IsAffine (Over.mk g).left := ‹IsAffine V›
  have h : V.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(V, ⊤))) = g :=
    affineBaseSectionsSpecIso_over R (Over.mk g)
  have hh : Spec.map (CommRingCat.ofHom (algebraMap R Γ(V, ⊤))) =
      V.isoSpec.inv ≫ g := by rw [← h, Iso.inv_hom_id_assoc]
  apply RingHom.finite_algebraMap.mp
  apply (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap R Γ(V, ⊤)))).mp
  rw [hh]
  infer_instance

variable [Algebra.FiniteType ℤ R] [Etale g] [IsFinite g]

/-- Every base point has a local finite basis of the actual translation coordinate algebra. -/
theorem exists_section_principal_basis (p : PrimeSpectrum R) :
    let _ := affineBaseSectionAlgebra g
    ∃ r : R, r ∉ p.asIdeal ∧ ∃ n : ℕ,
      Nonempty (Basis (Fin n) (Localization.Away r)
        (Localization.Away r ⊗[R] Γ(V, ⊤))) := by
  let _ := affineBaseSectionAlgebra g
  let _ := sectionAlgebra_etale g
  let _ := sectionAlgebra_finite g
  let _ := Algebra.FiniteType.isNoetherianRing ℤ R
  exact exists_etale_principal_basis p

/-- The constructed chart norm tests every point of its full translation fiber. -/
theorem exists_section_norm_chart (p : PrimeSpectrum R) :
    let _ := affineBaseSectionAlgebra g
    ∃ r : R, r ∉ p.asIdeal ∧ ∃ n : ℕ,
      ∃ _b : Basis (Fin n) (Localization.Away r) (Localization.Away r ⊗[R] Γ(V, ⊤)),
      ∀ (s : Localization.Away r ⊗[R] Γ(V, ⊤)) (q : PrimeSpectrum (Localization.Away r)),
        q ∈ PrimeSpectrum.basicOpen (Algebra.norm (Localization.Away r) s) ↔
          ∀ z : PrimeSpectrum (Localization.Away r ⊗[R] Γ(V, ⊤)),
            PrimeSpectrum.comap (algebraMap _ _) z = q → z ∈ PrimeSpectrum.basicOpen s := by
  let _ := affineBaseSectionAlgebra g
  obtain ⟨r, hr, n, ⟨b⟩⟩ := exists_section_principal_basis g p
  exact ⟨r, hr, n, b, fun s q ↦ mem_basicOpen_norm_iff b q s⟩

end FLT.Mazur.EtaleTranslationBranch

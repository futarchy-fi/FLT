/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Tate cohomology under a group equivalence

Reindex cochains by the group equivalence and chains by its inverse. The norm
sum is unchanged, so these maps join to an isomorphism of the actual Tate complexes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology groupHomology

variable {k G H : Type} [CommRing k] [Group G] [Group H]
  (M : Rep k G) (e : H ≃* G)

/-- The identity on coefficients after restricting along mutually inverse group maps. -/
def groupEquivalenceCoefficients : M ⟶ Rep.res e.symm.toMonoidHom (Rep.res e.toMonoidHom M) :=
  Rep.ofHom ⟨LinearMap.id, fun g => by ext x; simp⟩

/-- The coefficient comparison is bijective on underlying modules. -/
theorem groupEquivalenceCoefficients_bijective :
    Function.Bijective (groupEquivalenceCoefficients M e).hom := Function.bijective_id

variable [Fintype G] [Fintype H]

/-- Group equivalence preserves the finite norm sum. -/
theorem groupEquivalence_norm (x : M) :
    (Rep.res e.toMonoidHom M).norm.hom x = M.norm.hom x := by
  change (∑ h : H, M.ρ (e h)) x = (∑ g : G, M.ρ g) x
  simp only [LinearMap.sum_apply]
  exact e.toEquiv.sum_comp (fun g => M.ρ g x)

/-- The cochain and chain reindexings commute with the norm splice. -/
theorem groupEquivalence_norm_square :
    (chainsMap e.symm.toMonoidHom (groupEquivalenceCoefficients M e)).f 0 ≫
        (Rep.res e.toMonoidHom M).tateNorm =
      M.tateNorm ≫ (cochainsMap e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom M))).f 0 := by
  rw [← cancel_mono (cochainsIso₀ (Rep.res e.toMonoidHom M)).hom]
  simp only [Rep.tateNorm, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    cochainsMap_f_0_comp_cochainsIso₀, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, chainsMap_f_0_comp_chainsIso₀]
  ext x
  exact groupEquivalence_norm M e _

/-- Reindexing both halves of the Tate complex along a group equivalence. -/
def tateGroupEquivalenceMap : tateComplex M ⟶ tateComplex (Rep.res e.toMonoidHom M) :=
  CochainComplex.ConnectData.map _ _
    (chainsMap e.symm.toMonoidHom (groupEquivalenceCoefficients M e))
    (cochainsMap e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom M)))
    (groupEquivalence_norm_square M e)

/-- Every component of the reindexing map is invertible. -/
theorem tateGroupEquivalenceMap_isIso : IsIso (tateGroupEquivalenceMap M e) := by
  have : Mono (groupEquivalenceCoefficients M e) :=
    (Rep.mono_iff_injective _).mpr (groupEquivalenceCoefficients_bijective M e).1
  have : Epi (groupEquivalenceCoefficients M e) :=
    (Rep.epi_iff_surjective _).mpr (groupEquivalenceCoefficients_bijective M e).2
  have hc (i : ℕ) : IsIso ((cochainsMap e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom M))).f i) := by
    have := cochainsMap_f_map_mono e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom M)) e.surjective i
    have := cochainsMap_f_map_epi e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom M)) e.injective i
    exact isIso_of_mono_of_epi _
  have hh (i : ℕ) :
      IsIso ((chainsMap e.symm.toMonoidHom (groupEquivalenceCoefficients M e)).f i) := by
    have := chainsMap_f_map_mono e.symm.toMonoidHom
      (groupEquivalenceCoefficients M e) e.symm.injective i
    have := chainsMap_f_map_epi e.symm.toMonoidHom
      (groupEquivalenceCoefficients M e) e.symm.surjective i
    exact isIso_of_mono_of_epi _
  have (i : ℤ) : IsIso ((tateGroupEquivalenceMap M e).f i) := by
    cases i with
    | ofNat i => exact hc i
    | negSucc i => exact hh i
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Group equivalence induces an isomorphism in every integer Tate degree. -/
def tateGroupEquivalenceIso (n : ℤ) :
    tateCohomology M n ≅ tateCohomology (Rep.res e.toMonoidHom M) n := by
  letI := tateGroupEquivalenceMap_isIso M e
  exact HomologicalComplex.homologyMapIso (asIso (tateGroupEquivalenceMap M e)) n

end LocalClassFieldTheory

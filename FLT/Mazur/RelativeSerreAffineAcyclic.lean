/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicPushforwardCohomology
public import FLT.Mazur.HigherDirectImageOpenSheafification
public import FLT.Mazur.RelativeSerreAffineVanishing
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Sheafify

/-!
# Affine relative Serre acyclicity

Vanishing on a basis kills the stalks of the open cohomology presheaf and
therefore its sheafification. The actual module higher direct images then
vanish by the abelian comparison and faithful forgetting.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open FLT.Mazur.FCurve FLT.Mazur.HigherDirectImageOpenSheafification

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

namespace FLT.Mazur.ProjectiveSpace

/-- A presheaf zero on a basis has zero sheafification. -/
theorem isZero_sheafification_of_basis {X : TopCat.{u}} (F : X.Presheaf AddCommGrpCat.{u})
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hF : ∀ U ∈ B, Subsingleton (F.obj (op U))) :
    IsZero ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj F) := by
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
  intro x
  have hz : IsZero (F.stalk x) := by
    apply AddCommGrpCat.isZero_iff_subsingleton.mpr
    apply subsingleton_of_forall_eq 0
    intro t
    obtain ⟨U, hx, hU, s, rfl⟩ :=
      TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hB F x t
    have := hF U hU
    rw [Subsingleton.elim s 0]
    exact map_zero (F.germ U x hx).hom
  let := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} F
  exact hz.of_iso (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    (toSheafify (Opens.grothendieckTopology X) F))).symm

/-- Vanishing of actual restricted-module cohomology on a basis detects acyclicity. -/
theorem modulePushforwardAcyclic_of_basis {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules)
    {B : Set Y.Opens} (hB : Opens.IsBasis B)
    (hM : ∀ U ∈ B, ∀ q : ℕ, Subsingleton (ModuleH (M.restrict (f ⁻¹ᵁ U).ι) (q + 1))) :
    ModulePushforwardAcyclic f M := by
  intro q
  apply ModuleDerivedAbelianComparison.isZero_module_of_abelian
  apply IsZero.of_iso _ (moduleOpenComparison f M (q + 1))
  apply isZero_sheafification_of_basis _ hB
  intro U hU
  have := hM U hU q
  exact (moduleValueEquiv f M U (q + 1)).injective.subsingleton

/-- One affine Serre bound annihilates every positive actual module higher direct image. -/
theorem exists_affine_line_power_acyclic {R : Type} [CommRing R] [IsNoetherianRing R]
    {X : Scheme} {d : ℕ} (f : X ⟶ Spec (.of R))
    (i : X ⟶ space R (Fin (d + 1))) [IsClosedImmersion i]
    (hf : i ≫ baseProjection R _ = f) (L : X.Modules) (D : AffineLineCoefficients i L) :
    ∃ N : ℕ, ∀ n ≥ N,
      ModulePushforwardAcyclic f (ModuleLineBundleTensorPullback.tensorPower L n) := by
  obtain ⟨N, hN⟩ := exists_affine_line_power_moduleH_subsingleton f i hf L D
  refine ⟨N, fun n hn ↦ modulePushforwardAcyclic_of_basis f _
    PrimeSpectrum.isBasis_basic_opens ?_⟩
  rintro U ⟨r, rfl⟩ q
  exact hN n hn r q

/-- The affine conclusion is unchanged by a chosen identification of the target with a spectrum. -/
theorem exists_affine_line_power_acyclic_of_iso {R : Type} [CommRing R] [IsNoetherianRing R]
    {X Y : Scheme} {d : ℕ} (f : X ⟶ Y) (e : Y ≅ Spec (.of R))
    (i : X ⟶ space R (Fin (d + 1))) [IsClosedImmersion i]
    (hf : i ≫ baseProjection R _ = f ≫ e.hom) (L : X.Modules)
    (D : AffineLineCoefficients i L) :
    ∃ N : ℕ, ∀ n ≥ N,
      ModulePushforwardAcyclic f (ModuleLineBundleTensorPullback.tensorPower L n) := by
  obtain ⟨N, hN⟩ := exists_affine_line_power_moduleH_subsingleton (f ≫ e.hom) i hf L D
  have hB := PrimeSpectrum.isBasis_basic_opens (R := R) |>.of_isInducing
    e.hom.isOpenEmbedding.isEmbedding.isInducing
  refine ⟨N, fun n hn ↦ modulePushforwardAcyclic_of_basis f _ hB ?_⟩
  rintro U ⟨V, ⟨r, rfl⟩, rfl⟩ q
  exact hN n hn r q

end FLT.Mazur.ProjectiveSpace

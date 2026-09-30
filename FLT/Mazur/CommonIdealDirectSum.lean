/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentGenericCoordinates
public import FLT.Mazur.IdealPowerExtensionGluing

/-!
# A common ideal for a generic free comparison

Finite sums of the actual ideal module identify with the ideal-action image
on the finite free sheaf. A power of the vanishing ideal of the comparison
complement therefore supplies one global source for the comparison.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage
open FLT.Mazur.CoherentGenericCoordinates FLT.Mazur.CoherentIdealIntersection
open FLT.Mazur.GlobalIdealPower FLT.Mazur.GlobalIdealPowerCompatibility

universe u

namespace FLT.Mazur.CommonIdealDirectSum

variable {X : Scheme.{u}}

attribute [local instance] HasBiproduct.of_hasProduct

/-- The finite sum of copies of the actual ideal module. -/
abbrev idealSum (I : X.IdealSheafData) (r : ℕ) : X.Modules :=
  ∐ (fun _ : ULift.{u} (Fin r) ↦ idealModule I)

/-- Finite sums of module sheaves are also products. -/
def sumProductIso (M : X.Modules) (r : ℕ) :
    (∐ fun _ : ULift.{u} (Fin r) ↦ M) ≅ ∏ᶜ (fun _ : ULift.{u} (Fin r) ↦ M) :=
  (biproduct.isoCoproduct _).symm ≪≫ biproduct.isoProduct _

/-- The inclusion of the ideal in each coordinate of the finite free sheaf. -/
def sumInclusion (I : X.IdealSheafData) (r : ℕ) : idealSum I r ⟶ finiteFree X r :=
  (sumProductIso (idealModule I) r).hom ≫ Limits.Pi.map (fun _ ↦ idealModuleι I) ≫
    (finiteFreeProductIso X r).inv

instance sumInclusion_mono (I : X.IdealSheafData) (r : ℕ) :
    Mono (sumInclusion I r) := by dsimp only [sumInclusion]; infer_instance

/-- Coordinates of sections of a finite sum, through the preserved finite product. -/
def sumSections (M : X.Modules) (r : ℕ) (U : X.Opens) :
    Γ(∐ (fun _ : ULift.{u} (Fin r) ↦ M), U) ≃ₗ[Γ(X, U)]
      (ULift.{u} (Fin r) → Γ(M, U)) :=
  ((SheafOfModules.evaluation X.ringCatSheaf (op U)).mapIso (sumProductIso M r) ≪≫
    PreservesProduct.iso (SheafOfModules.evaluation X.ringCatSheaf (op U)) _ ≪≫
      ModuleCat.piIsoPi _).toLinearEquiv

/-- The section coordinates intertwine the actual ideal inclusions. -/
lemma sumSections_inclusion (I : X.IdealSheafData) (r : ℕ) (U : X.Opens)
    (s : Γ(idealSum I r, U)) (i : ULift.{u} (Fin r)) :
    sumSections (structureModule X) r U ((sumInclusion I r).app U s) i =
      (idealModuleι I).app U (sumSections (idealModule I) r U s i) := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U)
  have h (M : X.Modules) : (sumSections M r U).toModuleIso.hom ≫
      ModuleCat.ofHom (LinearMap.proj i) =
        E.map ((sumProductIso M r).hom ≫ Pi.π _ i) := by
    simp [sumSections, ← Functor.map_comp, PreservesProduct.iso_hom, E]
  have hn : E.map (sumInclusion I r) ≫ (sumSections (structureModule X) r U).toModuleIso.hom ≫
      ModuleCat.ofHom (LinearMap.proj i) =
        (sumSections (idealModule I) r U).toModuleIso.hom ≫
          ModuleCat.ofHom (LinearMap.proj i) ≫ E.map (idealModuleι I) := by
    rw [h, ← Category.assoc, h, ← Functor.map_comp, ← Functor.map_comp]
    congr 1
    change (sumProductIso (idealModule I) r).hom ≫
      Limits.Pi.map (fun _ ↦ idealModuleι I) ≫ (finiteFreeProductIso X r).inv ≫
        (finiteFreeProductIso X r).hom ≫ Pi.π _ i = _
    simp only [Iso.inv_hom_id_assoc, Pi.map_π, Category.assoc]
  exact congr($(hn) s)

/-- Coordinate membership detects the ideal multiple of a finite free module. -/
lemma mem_smul_iff {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (J : Ideal R) (r : ℕ) (e : M ≃ₗ[R] (ULift.{u} (Fin r) → R)) (s : M) :
    s ∈ J • (⊤ : Submodule R M) ↔ ∀ i, e s i ∈ J := by
  classical
  constructor
  · intro hs
    refine Submodule.smul_induction_on hs (fun a ha m _ i ↦ ?_) (fun x y hx hy i ↦ ?_)
    · simpa using J.mul_mem_right (e m i) ha
    · simpa using J.add_mem (hx i) (hy i)
  · intro hs
    have he : s = ∑ i, e s i • e.symm (Pi.single i 1) := by
      apply e.injective
      simp [map_sum, ← Pi.single_smul, Finset.univ_sum_single]
    rw [he]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hs i) Submodule.mem_top

/-- The finite ideal sum has exactly the affine image of the ideal-action map. -/
lemma sumInclusion_range (I : X.IdealSheafData) (r : ℕ) (V : X.affineOpens) :
    LinearMap.range ((sumInclusion I r).val.app (op V.1)).hom =
      I.ideal V • (⊤ : Submodule Γ(X, V.1) Γ(finiteFree X r, V.1)) := by
  ext s
  rw [mem_smul_iff (I.ideal V) r (sumSections (structureModule X) r V.1)]
  constructor
  · rintro ⟨t, rfl⟩ i
    change sumSections (structureModule X) r V.1 ((sumInclusion I r).app V.1 t) i ∈ _
    rw [sumSections_inclusion, ← idealModuleAffineEquiv_val]
    exact (idealModuleAffineEquiv I V _).property
  · intro hs
    let t := (sumSections (idealModule I) r V.1).symm
      (fun i ↦ (idealModuleAffineEquiv I V).symm ⟨_, hs i⟩)
    refine ⟨t, ?_⟩
    apply (sumSections (structureModule X) r V.1).injective
    funext i
    change sumSections (structureModule X) r V.1 ((sumInclusion I r).app V.1 t) i = _
    rw [sumSections_inclusion, ← idealModuleAffineEquiv_val]
    dsimp only [t]
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rfl

/-- The canonical identification preserves the inclusion into the original finite free sheaf. -/
def multipleSumIso [IsLocallyNoetherian X] (I : X.IdealSheafData) (r : ℕ) :
    multiple I (finiteFree X r) ≅ idealSum I r :=
  affineImageIso (inclusion I (finiteFree X r)) (sumInclusion I r)
    (fun V ↦ (inclusion_range I _ V).trans (sumInclusion_range I r V).symm)

@[reassoc (attr := simp)]
lemma multipleSumIso_comp [IsLocallyNoetherian X] (I : X.IdealSheafData) (r : ℕ) :
    (multipleSumIso I r).hom ≫ sumInclusion I r = inclusion I (finiteFree X r) :=
  affineImageIso_comp _ _ _

/-- The actual ideal cutting out the complement of an open comparison. -/
def comparisonIdeal (U : X.Opens) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal U.compl

@[simp]
lemma comparisonIdeal_complement (U : X.Opens) : complement (comparisonIdeal U) = U := by
  change U.compl.compl = U
  exact U.compl_compl

/-- Every power is nonzero when the comparison open contains a point. -/
lemma comparisonIdeal_power_ne_bot (U : X.Opens) (x : X) (hx : x ∈ U) (n : ℕ) :
    comparisonIdeal U ^ n ≠ ⊥ := by
  intro h
  have hs : x ∉ (comparisonIdeal U ^ n).support := by
    cases n with
    | zero => simpa only [pow_zero, Scheme.IdealSheafData.one_eq_top,
        Scheme.IdealSheafData.support_top] using (show x ∉ (⊥ : Closeds X) from fun h ↦ h)
    | succ n => exact not_not_intro hx
  rw [h] at hs
  exact hs trivial

/-- The common power and its map are constructed from the original open comparison. -/
theorem exists_sum_extension [IsNoetherian X] (U : X.Opens) (r : ℕ)
    (G : X.Modules) [G.IsFinitePresentation]
    (g : (finiteFree X r).restrict U.ι ⟶ G.restrict U.ι) :
    ∃ n : ℕ, ∃ f : idealSum (comparisonIdeal U ^ n) r ⟶ G,
      (restrictFunctor U.ι).map f =
        (restrictFunctor U.ι).map (sumInclusion (comparisonIdeal U ^ n) r) ≫ g := by
  have hex := IdealPowerExtensionGluing.exists_ideal_power_extension
    (comparisonIdeal U) (finiteFree X r) G
  rw [comparisonIdeal_complement] at hex
  obtain ⟨n, f, hf⟩ := hex g
  refine ⟨n, (multipleSumIso (comparisonIdeal U ^ n) r).inv ≫ f, ?_⟩
  rw [Functor.map_comp, hf, ← Category.assoc, ← Functor.map_comp]
  congr 2
  exact (Iso.inv_comp_eq _).mpr (multipleSumIso_comp _ _).symm

/-- On the comparison open, the actual finite ideal-sum inclusion is invertible. -/
theorem sumInclusion_comparison_isIso [IsLocallyNoetherian X] (U : X.Opens)
    (n r : ℕ) : IsIso ((restrictFunctor U.ι).map
      (sumInclusion (comparisonIdeal U ^ n) r)) := by
  have hi := power_inclusion_complement (comparisonIdeal U) n (finiteFree X r)
  rw [comparisonIdeal_complement] at hi
  have h : sumInclusion (comparisonIdeal U ^ n) r =
      (multipleSumIso (comparisonIdeal U ^ n) r).inv ≫
        inclusion (comparisonIdeal U ^ n) (finiteFree X r) := by
    rw [← multipleSumIso_comp, Iso.inv_hom_id_assoc]
  rw [h, Functor.map_comp]
  infer_instance

/-- Transport the constructed generic comparison to the actual image open. -/
theorem exists_generic_open_comparison [IsLocallyNoetherian X] [IsIntegral X]
    (G : X.Modules) [G.IsFinitePresentation] :
    ∃ U : X.Opens, genericPoint X ∈ U ∧ ∃ g :
      (finiteFree X (Module.finrank X.functionField
        (G.presheaf.stalk (genericPoint X)))).restrict U.ι ⟶ G.restrict U.ι, IsIso g := by
  obtain ⟨C, hC, _, _⟩ := exists_generic_free_comparison G
  let k := C.inclusion.isoOpensRange.inv
  let q := (restrictFunctorComp k C.inclusion).symm ≪≫
    restrictFunctorCongr C.inclusion.isoOpensRange_inv_comp
  refine ⟨C.inclusion.opensRange, ?_,
    q.inv.app _ ≫ (restrictFunctor k).map C.map ≫ q.hom.app G, ?_⟩
  · exact ⟨C.point, C.point_eq⟩
  · infer_instance

/-- One nonzero ideal and its finite direct sum realize the generic comparison globally. -/
theorem exists_common_ideal [IsNoetherian X] [IsIntegral X]
    (G : X.Modules) [G.IsFinitePresentation] :
    ∃ (U : X.Opens), genericPoint X ∈ U ∧ ∃ n : ℕ,
      comparisonIdeal U ^ n ≠ ⊥ ∧ ∃ f :
        idealSum (comparisonIdeal U ^ n) (Module.finrank X.functionField
          (G.presheaf.stalk (genericPoint X))) ⟶ G,
        IsIso ((restrictFunctor U.ι).map f) := by
  obtain ⟨U, hx, g, hg⟩ := exists_generic_open_comparison G
  obtain ⟨n, f, hf⟩ := exists_sum_extension U _ G g
  refine ⟨U, hx, n, comparisonIdeal_power_ne_bot U _ hx n, f, ?_⟩
  rw [hf]
  have := sumInclusion_comparison_isIso U n
    (Module.finrank X.functionField (G.presheaf.stalk (genericPoint X)))
  infer_instance

end FLT.Mazur.CommonIdealDirectSum

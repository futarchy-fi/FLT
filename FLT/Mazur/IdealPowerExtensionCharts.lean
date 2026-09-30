/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GlobalIdealPowerCompatibility

/-!
# Ideal-power extensions in actual affine charts

The complement of the coordinate ideal is the inverse image of the global
comparison open. The affine extension theorem therefore constructs maps from
the restrictions of the actual global ideal-power image.

Finite affine refinements also construct global equalizers, and nested powers
convert their equations to transitions between single powers. Compatibility
of the chosen chart extensions and their final gluing remain separate steps.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage
open FLT.Mazur.GlobalIdealPower FLT.Mazur.GlobalIdealPowerCompatibility
open FLT.Mazur.AffineIdealPowerExtension (idealComplement)
open FLT.Mazur.CoherentSubmoduleEnlargement

universe u

namespace FLT.Mazur.IdealPowerExtensionCharts

variable {X Y : Scheme.{u}}

/-- The complement of an ideal commutes with inverse image. -/
lemma complement_comap (I : X.IdealSheafData) (j : Y ⟶ X) :
    complement (I.comap j) = j ⁻¹ᵁ complement I := by
  unfold complement
  rw [Scheme.IdealSheafData.support_comap]
  rfl

/-- The spectrum coordinate ideal defines exactly the original comparison open. -/
lemma spec_complement {R : CommRingCat.{u}} (I : (Spec R).IdealSheafData) :
    complement I = idealComplement (specIdeal I) := by
  apply Opens.ext
  apply congrArg Set.compl
  have h := Scheme.IdealSheafData.coe_support_inter I ⟨⊤, isAffineOpen_top _⟩
  simp only [Opens.coe_top, Set.inter_univ] at h
  rw [h, Spec_zeroLocus]
  congr 1
  let e := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  change _ = ((I.ideal ⟨⊤, isAffineOpen_top _⟩).map e : Set R)
  exact congrArg (fun J : Ideal R ↦ (J : Set R))
    (Ideal.map_comap_of_equiv (I := I.ideal ⟨⊤, isAffineOpen_top _⟩) e).symm

/-- The given open comparison transported through the actual open base-change square. -/
def pullComparison (j : Y ⟶ X) [IsOpenImmersion j] (U : X.Opens)
    {M N : X.Modules} (g : M.restrict U.ι ⟶ N.restrict U.ι) :
    (M.restrict j).restrict (j ⁻¹ᵁ U).ι ⟶ (N.restrict j).restrict (j ⁻¹ᵁ U).ι :=
  (restrictionSquare j U).inv.app M ≫ (restrictFunctor (j ∣_ U)).map g ≫
    (restrictionSquare j U).hom.app N

/-- Transporting a restricted global map recovers its restriction in the chart. -/
lemma pullComparison_map (j : Y ⟶ X) [IsOpenImmersion j] (U : X.Opens)
    {M N : X.Modules} (f : M ⟶ N) :
    pullComparison j U ((restrictFunctor U.ι).map f) =
      (restrictFunctor (j ⁻¹ᵁ U).ι).map ((restrictFunctor j).map f) := by
  unfold pullComparison
  rw [← Functor.comp_map, (restrictionSquare j U).hom.naturality,
    Iso.inv_hom_id_app_assoc]
  rfl

/-- Pulling back comparisons preserves composition. -/
lemma pullComparison_comp (j : Y ⟶ X) [IsOpenImmersion j] (U : X.Opens)
    {L M N : X.Modules} (f : L.restrict U.ι ⟶ M.restrict U.ι)
    (g : M.restrict U.ι ⟶ N.restrict U.ι) :
    pullComparison j U (f ≫ g) = pullComparison j U f ≫ pullComparison j U g := by
  simp [pullComparison, Functor.map_comp, Category.assoc]

/-- A finite family of spectrum comparisons extends from the constructed ideal images. -/
theorem exists_spec_extensions {ι : Type u} [Finite ι] (R : ι → CommRingCat.{u})
    [∀ i, IsNoetherianRing (R i)] (I : ∀ i, (Spec (R i)).IdealSheafData)
    (M N : ∀ i, (Spec (R i)).Modules)
    [∀ i, (M i).IsFinitePresentation] [∀ i, (N i).IsFinitePresentation]
    (g : ∀ i, (M i).restrict (complement (I i)).ι ⟶
      (N i).restrict (complement (I i)).ι) :
    ∃ n : ℕ, ∀ i, ∃ f : power (I i) n (M i) ⟶ N i,
      (restrictFunctor (complement (I i)).ι).map f =
        (restrictFunctor (complement (I i)).ι).map (inclusion ((I i) ^ n) (M i)) ≫ g i := by
  let P (U : ∀ i, (Spec (R i)).Opens) : Prop :=
    ∀ g : ∀ i, (M i).restrict (U i).ι ⟶ (N i).restrict (U i).ι,
      ∃ n : ℕ, ∀ i, ∃ f : power (I i) n (M i) ⟶ N i,
        (restrictFunctor (U i).ι).map f =
          (restrictFunctor (U i).ι).map (inclusion ((I i) ^ n) (M i)) ≫ g i
  suffices h : P (fun i ↦ idealComplement (specIdeal (I i))) by
    have he := funext (fun i ↦ spec_complement (I i))
    rw [← he] at h
    exact h g
  intro g
  obtain ⟨n, hn⟩ := IdealPowerCompatibility.exists_common_extensions R M N
    (fun i ↦ specIdeal (I i)) (fun i ↦ IsNoetherian.noetherian _) g
  refine ⟨n, fun i ↦ ?_⟩
  obtain ⟨f, hf⟩ := hn i
  refine ⟨(specPowerIso (I i) n (M i)).hom ≫ f, ?_⟩
  rw [Functor.map_comp, hf, ← Category.assoc, ← Functor.map_comp,
    specPowerIso_inclusion]

/-- Actual spectrum charts of a global comparison have one common extension exponent. -/
theorem exists_chart_extensions [IsLocallyNoetherian X]
    {ι : Type u} [Finite ι] (R : ι → CommRingCat.{u})
    (j : ∀ i, Spec (R i) ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (I : X.IdealSheafData) (M N : X.Modules)
    [M.IsFinitePresentation] [N.IsFinitePresentation]
    (g : M.restrict (complement I).ι ⟶ N.restrict (complement I).ι) :
    ∃ n : ℕ, ∀ i, ∃ f : (power I n M).restrict (j i) ⟶ N.restrict (j i),
      (restrictFunctor (j i ⁻¹ᵁ complement I).ι).map f =
        (restrictFunctor (j i ⁻¹ᵁ complement I).ι).map
          ((restrictFunctor (j i)).map (inclusion (I ^ n) M)) ≫
            pullComparison (j i) (complement I) g := by
  have (i : ι) : IsLocallyNoetherian (Spec (R i)) :=
    LocallyOfFiniteType.isLocallyNoetherian (j i)
  have (i : ι) : IsNoetherianRing (R i) :=
    isLocallyNoetherian_Spec.mp inferInstance
  have (i : ι) := coherentPresentation_restrict (j i) M
  have (i : ι) := coherentPresentation_restrict (j i) N
  have h := exists_spec_extensions R (fun i ↦ I.comap (j i))
    (fun i ↦ M.restrict (j i)) (fun i ↦ N.restrict (j i))
  let P (U : ∀ i, (Spec (R i)).Opens) : Prop :=
    ∀ g : ∀ i, (M.restrict (j i)).restrict (U i).ι ⟶
        (N.restrict (j i)).restrict (U i).ι,
      ∃ n : ℕ, ∀ i, ∃ f : power (I.comap (j i)) n (M.restrict (j i)) ⟶ N.restrict (j i),
        (restrictFunctor (U i).ι).map f =
          (restrictFunctor (U i).ι).map (inclusion ((I.comap (j i)) ^ n)
            (M.restrict (j i))) ≫ g i
  change P (fun i ↦ complement (I.comap (j i))) at h
  rw [funext (fun i ↦ complement_comap I (j i))] at h
  obtain ⟨n, hn⟩ := h (fun i ↦ pullComparison (j i) (complement I) g)
  refine ⟨n, fun i ↦ ?_⟩
  obtain ⟨f, hf⟩ := hn i
  refine ⟨(powerRestrictIso I n M (j i)).hom ≫ f, ?_⟩
  rw [Functor.map_comp, hf, ← Category.assoc, ← Functor.map_comp,
    powerRestrictIso_comp]

/-- Choose a finite cover by actual affine opens of a Noetherian scheme. -/
theorem exists_finite_affine_cover [IsNoetherian X] :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → X.affineOpens), ⨆ i, (V i).1 = ⊤ := by
  let C := X.affineCover.finiteSubcover
  have hV (i : C.I₀) : IsAffineOpen (C.f i).opensRange := by
    have : IsAffine (C.X i) := by
      change IsAffine (X.affineCover.finiteSubcover.X i)
      rw [X.affineCover.finiteSubcover_X]
      infer_instance
    exact isAffineOpen_opensRange (C.f i)
  exact ⟨C.I₀, inferInstance, fun i ↦ ⟨(C.f i).opensRange, hV i⟩, C.iSup_opensRange⟩

/-- The cover, exponent, and chart extensions all come from the original global comparison. -/
theorem exists_cover_extensions [IsNoetherian X] (I : X.IdealSheafData) (M N : X.Modules)
    [M.IsFinitePresentation] [N.IsFinitePresentation]
    (g : M.restrict (complement I).ι ⟶ N.restrict (complement I).ι) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → X.affineOpens),
      (⨆ i, (V i).1) = ⊤ ∧ ∃ n : ℕ, ∀ i,
        ∃ f : (power I n M).restrict (V i).2.fromSpec ⟶ N.restrict (V i).2.fromSpec,
          (restrictFunctor ((V i).2.fromSpec ⁻¹ᵁ complement I).ι).map f =
            (restrictFunctor ((V i).2.fromSpec ⁻¹ᵁ complement I).ι).map
              ((restrictFunctor (V i).2.fromSpec).map (inclusion (I ^ n) M)) ≫
                pullComparison (V i).2.fromSpec (complement I) g := by
  obtain ⟨ι, hι, V, hV⟩ := exists_finite_affine_cover (X := X)
  exact ⟨ι, hι, V, hV, exists_chart_extensions (fun i ↦ Γ(X, (V i).1))
    (fun i ↦ (V i).2.fromSpec) I M N g⟩

/-- Open-immersion charts detect equality on the original scheme. -/
lemma hom_ext_charts {ι : Type u} (Y : ι → Scheme.{u}) (j : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hcover : ⨆ i, (j i).opensRange = ⊤)
    {M N : X.Modules} (f g : M ⟶ N)
    (h : ∀ i, (restrictFunctor (j i)).map f = (restrictFunctor (j i)).map g) : f = g := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  apply ModuleSheafMorphismGluing.section_ext (fun i ↦ (j i).opensRange) hcover U
  intro i
  rw [← ModuleSubobjectCoverEquality.app_res, ← ModuleSubobjectCoverEquality.app_res]
  have he : j i ''ᵁ (j i ⁻¹ᵁ U) = U ⊓ (j i).opensRange := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_comm]
  have hh := congrArg (fun a ↦ a.app (j i ⁻¹ᵁ U)) (h i)
  change f.app (j i ''ᵁ (j i ⁻¹ᵁ U)) = g.app (j i ''ᵁ (j i ⁻¹ᵁ U)) at hh
  rw [he] at hh
  exact congr($(hh) (ModuleSheafMorphismGluing.res M inf_le_left s))

/-- A finite family of affine differences is killed on the actual ideal-action images. -/
theorem exists_spec_equalizers {ι : Type u} [Finite ι] (R : ι → CommRingCat.{u})
    [∀ i, IsNoetherianRing (R i)] (I : ∀ i, (Spec (R i)).IdealSheafData)
    (M N : ∀ i, (Spec (R i)).Modules)
    [∀ i, (M i).IsFinitePresentation] [∀ i, (N i).IsQuasicoherent]
    (f g : ∀ i, M i ⟶ N i)
    (h : ∀ i, (restrictFunctor (complement (I i)).ι).map (f i) =
      (restrictFunctor (complement (I i)).ι).map (g i)) :
    ∃ n : ℕ, ∀ i, inclusion ((I i) ^ n) (M i) ≫ f i =
      inclusion ((I i) ^ n) (M i) ≫ g i := by
  have hh (i) : (restrictFunctor (idealComplement (specIdeal (I i))).ι).map (f i) =
      (restrictFunctor (idealComplement (specIdeal (I i))).ι).map (g i) := by
    rw [← spec_complement]
    exact h i
  obtain ⟨n, hn⟩ := IdealPowerCompatibility.exists_common_equalizers R M N
    (fun i ↦ specIdeal (I i)) (fun i ↦ IsNoetherian.noetherian _) f g hh
  refine ⟨n, fun i ↦ ?_⟩
  rw [← specPowerIso_inclusion (I i) n (M i), Category.assoc, hn i, Category.assoc]

/-- Two global maps agreeing off an ideal agree on a constructed power multiple. -/
theorem exists_global_equalizer [IsNoetherian X] (I : X.IdealSheafData)
    {M N : X.Modules} [M.IsFinitePresentation] [N.IsFinitePresentation] (f g : M ⟶ N)
    (h : (restrictFunctor (complement I).ι).map f =
      (restrictFunctor (complement I).ι).map g) :
    ∃ n : ℕ, inclusion (I ^ n) M ≫ f = inclusion (I ^ n) M ≫ g := by
  obtain ⟨ι, hι, V, hV⟩ := exists_finite_affine_cover (X := X)
  let j := fun i ↦ (V i).2.fromSpec
  have (i : ι) : IsNoetherianRing Γ(X, (V i).1) :=
    IsLocallyNoetherian.component_noetherian (V i)
  have (i : ι) := coherentPresentation_restrict (j i) M
  have (i : ι) := coherentPresentation_restrict (j i) N
  have hh (i) : (restrictFunctor (complement (I.comap (j i))).ι).map
      ((restrictFunctor (j i)).map f) = (restrictFunctor (complement (I.comap (j i))).ι).map
        ((restrictFunctor (j i)).map g) := by
    rw [complement_comap, ← pullComparison_map, ← pullComparison_map, h]
  obtain ⟨n, hn⟩ := exists_spec_equalizers (fun i ↦ Γ(X, (V i).1))
    (fun i ↦ I.comap (j i)) (fun i ↦ M.restrict (j i)) (fun i ↦ N.restrict (j i))
    (fun i ↦ (restrictFunctor (j i)).map f) (fun i ↦ (restrictFunctor (j i)).map g) hh
  refine ⟨n, hom_ext_charts _ j (by simpa [j] using hV) _ _ (fun i ↦ ?_)⟩
  simp only [Functor.map_comp, ← powerRestrictIso_comp I n M (j i), Category.assoc]
  rw [hn i]

/-- A finite collection of global differences has a common equalizing exponent. -/
theorem exists_common_global_equalizers {ι : Type u} [Finite ι] (X : ι → Scheme.{u})
    [∀ i, IsNoetherian (X i)] (I : ∀ i, (X i).IdealSheafData)
    (M N : ∀ i, (X i).Modules)
    [∀ i, (M i).IsFinitePresentation] [∀ i, (N i).IsFinitePresentation]
    (f g : ∀ i, M i ⟶ N i)
    (h : ∀ i, (restrictFunctor (complement (I i)).ι).map (f i) =
      (restrictFunctor (complement (I i)).ι).map (g i)) :
    ∃ n : ℕ, ∀ i, inclusion ((I i) ^ n) (M i) ≫ f i =
      inclusion ((I i) ^ n) (M i) ≫ g i := by
  classical
  let indexFintype : Fintype ι := Fintype.ofFinite ι
  choose n hn using fun i ↦ exists_global_equalizer (I i) (f i) (g i) (h i)
  refine ⟨Finset.univ.sup n, fun i ↦ ?_⟩
  let hi : n i ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ i)
  rw [← transition_comp (I i) (M i) hi, Category.assoc, hn i, Category.assoc]

/-- Equalization on a nested image is equalization after increasing the original exponent. -/
lemma transition_equalizes_of_nested [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (M N : X.Modules) [M.IsFinitePresentation] (a b : ℕ)
    (f g : power I a M ⟶ N)
    (h : inclusion (I ^ b) (power I a M) ≫ f =
      inclusion (I ^ b) (power I a M) ≫ g) :
    transition I M (Nat.le_add_right a b) ≫ f =
      transition I M (Nat.le_add_right a b) ≫ g := by
  have ht : (nestedPowerIso I a b M).hom ≫ transition I M (Nat.le_add_right a b) =
      inclusion (I ^ b) (power I a M) := by
    apply (cancel_mono (inclusion (I ^ a) M)).mp
    rw [Category.assoc, transition_comp, nestedPowerIso_comp]
  apply (cancel_epi (nestedPowerIso I a b M).hom).mp
  rw [← Category.assoc, ht, ← Category.assoc, ht, h]

/-- Maps on an actual power source agreeing off the ideal agree at one higher power. -/
theorem exists_higher_equalizer [IsNoetherian X] (I : X.IdealSheafData)
    (M N : X.Modules) [M.IsFinitePresentation] [N.IsFinitePresentation] (a : ℕ)
    (f g : power I a M ⟶ N)
    (h : (restrictFunctor (complement I).ι).map f =
      (restrictFunctor (complement I).ι).map g) :
    ∃ b : ℕ, transition I M (Nat.le_add_right a b) ≫ f =
      transition I M (Nat.le_add_right a b) ≫ g := by
  obtain ⟨b, hb⟩ := exists_global_equalizer I f g h
  exact ⟨b, transition_equalizes_of_nested I M N a b f g hb⟩

end FLT.Mazur.IdealPowerExtensionCharts

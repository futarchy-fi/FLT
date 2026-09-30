/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealPowerChartDescent

/-!
# Global extension from an ideal-power multiple

A single exponent kills the differences of the constructed overlap maps.
The compatible affine-open maps then glue, with the prescribed comparison
on the complement of the ideal support.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage
open FLT.Mazur.GlobalIdealPower FLT.Mazur.GlobalIdealPowerCompatibility
open FLT.Mazur.IdealPowerExtensionCharts FLT.Mazur.IdealPowerChartDescent
open FLT.Mazur.CoherentSubmoduleEnlargement FLT.Mazur.ModuleSheafMorphismGluing
open FLT.Mazur.FCurve.CoherentDevissage.ClosedDescentCharts

universe u

namespace FLT.Mazur.IdealPowerExtensionGluing

variable {X Y : Scheme.{u}}

/-- Geometric overlap equality implies equality on every subopen of the slice site. -/
lemma compatible_of_overlap {ι : Type u} (V : ι → X.Opens) {P Q : X.Modules}
    (f : ∀ i, P.restrict (V i).ι ⟶ Q.restrict (V i).ι)
    (hf : ∀ i j, onOpen (inf_le_left : V i ⊓ V j ≤ V i) (f i) =
      onOpen (inf_le_right : V i ⊓ V j ≤ V j) (f j)) :
    Compatible V (fun i ↦ (restrictionEquiv (V i)).symm (f i)) := by
  have hs (i) : (restrictionEquiv (V i)).symm (f i) = sliceMap (V i) (f i) := by
    apply (restrictionEquiv (V i)).injective
    rw [Equiv.apply_symm_apply, sliceMap_restrictionEquiv]
  have hn {U W : X.Opens} (h : W ≤ U) (a : P.restrict U.ι ⟶ Q.restrict U.ι) :
      (restrictFunctor (X.homOfLE h)).map a ≫ (nestedRestriction h).hom.app Q =
        (nestedRestriction h).hom.app P ≫ onOpen h a := by
    rw [onOpen_nested]
    simp only [Iso.hom_inv_id_app_assoc]
  intro i j S hi hj
  dsimp only
  rw [hs, hs, sliceMap_nested inf_le_left (f i) _ (hn inf_le_left (f i)) S (le_inf hi hj),
    sliceMap_nested inf_le_right (f j) _ (hn inf_le_right (f j)) S (le_inf hi hj), hf]

/-- Equalization on the local power source transports to the restricted global transition. -/
lemma restricted_transition_equalizes [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (M N : X.Modules) [M.IsFinitePresentation] (a b : ℕ) (j : Y ⟶ X)
    [IsOpenImmersion j] (f g : (power I a M).restrict j ⟶ N.restrict j)
    (h : inclusion ((I.comap j) ^ b) (power (I.comap j) a (M.restrict j)) ≫
        (powerRestrictIso I a M j).inv ≫ f =
      inclusion ((I.comap j) ^ b) (power (I.comap j) a (M.restrict j)) ≫
        (powerRestrictIso I a M j).inv ≫ g) :
    (restrictFunctor j).map (transition I M (Nat.le_add_right a b)) ≫ f =
      (restrictFunctor j).map (transition I M (Nat.le_add_right a b)) ≫ g := by
  have := LocallyOfFiniteType.isLocallyNoetherian j
  have := coherentPresentation_restrict j M
  have he := transition_equalizes_of_nested (I.comap j) (M.restrict j) (N.restrict j)
    a b ((powerRestrictIso I a M j).inv ≫ f) ((powerRestrictIso I a M j).inv ≫ g) h
  have ht (q : (power I a M).restrict j ⟶ N.restrict j) :
      (restrictFunctor j).map (transition I M (Nat.le_add_right a b)) ≫ q =
        (powerRestrictIso I (a + b) M j).hom ≫
          transition (I.comap j) (M.restrict j) (Nat.le_add_right a b) ≫
            (powerRestrictIso I a M j).inv ≫ q := by
    rw [← Category.assoc, ← transition_restrict]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [ht f, ht g, he]

/-- The constructed affine-open extensions become compatible at one larger exponent. -/
theorem exists_compatible_extensions [IsNoetherian X] (I : X.IdealSheafData)
    (M N : X.Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (g : M.restrict (complement I).ι ⟶ N.restrict (complement I).ι) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → X.affineOpens),
      (⨆ i, (V i).1) = ⊤ ∧ ∃ n : ℕ, ∃ f : ∀ i,
        (power I n M).restrict (V i).1.ι ⟶ N.restrict (V i).1.ι,
        (∀ i, (restrictFunctor ((V i).1.ι ⁻¹ᵁ complement I).ι).map (f i) =
          pullComparison (V i).1.ι (complement I)
            ((restrictFunctor (complement I).ι).map (inclusion (I ^ n) M) ≫ g)) ∧
        ∀ i j, onOpen (inf_le_left : (V i).1 ⊓ (V j).1 ≤ (V i).1) (f i) =
          onOpen (inf_le_right : (V i).1 ⊓ (V j).1 ≤ (V j).1) (f j) := by
  obtain ⟨ι, hι, V, hV, a, f, hf, ho⟩ := exists_overlap_extensions I M N g
  let W := fun p : ι × ι ↦ (V p.1).1 ⊓ (V p.2).1
  have (p : ι × ι) : IsNoetherian (W p).toScheme := by
    have : NoetherianSpace (W p).toScheme :=
      (W p).ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    exact ⟨⟩
  let J := fun p ↦ I.comap (W p).ι
  let L := fun p ↦ power (J p) a (M.restrict (W p).ι)
  have (p : ι × ι) := coherentPresentation_restrict (W p).ι M
  have (p : ι × ι) := coherentPresentation_restrict (W p).ι N
  let e := fun p ↦ powerRestrictIso I a M (W p).ι
  let s := fun p ↦ (e p).inv ≫ onOpen inf_le_left (f p.1)
  let t := fun p ↦ (e p).inv ≫ onOpen inf_le_right (f p.2)
  have hst (p : ι × ι) : (restrictFunctor (complement (J p)).ι).map (s p) =
      (restrictFunctor (complement (J p)).ι).map (t p) := by
    dsimp only [s, t]
    rw [Functor.map_comp, Functor.map_comp, ho p.1 p.2]
  obtain ⟨b, hb⟩ := exists_common_global_equalizers (fun p ↦ (W p).toScheme) J L
    (fun p ↦ N.restrict (W p).ι) s t hst
  let q := transition I M (Nat.le_add_right a b)
  let f' := fun i ↦ (restrictFunctor (V i).1.ι).map q ≫ f i
  refine ⟨ι, hι, V, hV, a + b, f', ?_, ?_⟩
  · intro i
    dsimp only [f']
    rw [Functor.map_comp, hf, ← pullComparison_map, ← pullComparison_comp,
      ← Functor.map_comp_assoc, transition_comp]
  · intro i j
    dsimp only [f']
    rw [onOpen_comp, onOpen_comp, onOpen_map, onOpen_map]
    exact restricted_transition_equalizes I M N a b (W (i, j)).ι _ _ (hb (i, j))

/-- The inverse images of an open cover cover every comparison open. -/
lemma comparison_cover {ι : Type u} (V : ι → X.Opens) (hV : ⨆ i, V i = ⊤)
    (U : X.Opens) : ⨆ i, ((V i).ι ∣_ U).opensRange = ⊤ := by
  apply U.ι.image_injective
  dsimp only
  rw [Scheme.Hom.image_iSup, U.ι_image_top]
  have hi (i) : U.ι ''ᵁ ((V i).ι ∣_ U).opensRange = V i ⊓ U := by
    rw [← Scheme.Hom.opensRange_comp]
    simp only [morphismRestrict_ι, Scheme.Hom.opensRange_comp,
      Scheme.Opens.opensRange_ι, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
  simp_rw [hi]
  rw [← iSup_inf_eq, hV, top_inf_eq]

/-- The original comparison is detected by its transported squares on a cover. -/
lemma comparison_ext {ι : Type u} (V : ι → X.Opens) (hV : ⨆ i, V i = ⊤)
    (U : X.Opens) {P Q : X.Modules} (f g : P.restrict U.ι ⟶ Q.restrict U.ι)
    (h : ∀ i, pullComparison (V i).ι U f = pullComparison (V i).ι U g) : f = g := by
  apply hom_ext_charts _ (fun i ↦ (V i).ι ∣_ U) (comparison_cover V hV U)
  intro i
  simpa only [pullComparison, cancel_epi, cancel_mono] using h i

/-- An open comparison extends globally from a power of the original ideal acting on the source. -/
theorem exists_ideal_power_extension [IsNoetherian X] (I : X.IdealSheafData)
    (M N : X.Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (g : M.restrict (complement I).ι ⟶ N.restrict (complement I).ι) :
    ∃ n : ℕ, ∃ f : power I n M ⟶ N,
      (restrictFunctor (complement I).ι).map f =
        (restrictFunctor (complement I).ι).map (inclusion (I ^ n) M) ≫ g := by
  obtain ⟨ι, hι, V, hV, n, f, hf, ho⟩ := exists_compatible_extensions I M N g
  obtain ⟨F, hF, _⟩ := existsUnique_glue_restrict (fun i ↦ (V i).1) hV f
    (compatible_of_overlap (fun i ↦ (V i).1) f ho)
  refine ⟨n, F, comparison_ext (fun i ↦ (V i).1) hV (complement I) _ _ (fun i ↦ ?_)⟩
  rw [pullComparison_map, hF, hf]

end FLT.Mazur.IdealPowerExtensionGluing

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InjectiveHorseshoe
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Connecting maps for right-derived functors

The injective horseshoe supplies a degreewise split sequence. Applying an
additive functor and taking its homology sequence constructs connecting maps
for the actual right-derived functors, with exactness and dimension shifts.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open FLT.Mazur.InjectiveHorseshoe

namespace FLT.Mazur.RightDerivedDimensionShift

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [EnoughInjectives C] (S : ShortComplex C) (hS : S.ShortExact)
  (T : C ⥤ D) [T.Additive]

/-- The image under `T` of the internally constructed horseshoe. -/
def imageSequence : ShortComplex (CochainComplex D ℕ) :=
  (resolutionSequence S hS).map (T.mapHomologicalComplex _)

/-- Additivity preserves the splitting in each degree. -/
def imageSplitting (n : ℕ) :
    ((imageSequence S hS T).map (eval D (ComplexShape.up ℕ) n)).Splitting :=
  (degreeSplitting S hS n).map T

lemma image_shortExact : (imageSequence S hS T).ShortExact :=
  shortExact_of_degreewise_shortExact _ (fun n => (imageSplitting S hS T n).shortExact)

/-- Compute the derived objects of the left term on its constructed resolution. -/
abbrev leftIso (n : ℕ) := (leftResolution S hS).isoRightDerivedObj T n

/-- Compute the derived objects of the middle term on its constructed resolution. -/
abbrev middleIso (n : ℕ) := (middleResolution S hS).isoRightDerivedObj T n

/-- Compute the derived objects of the right term on its constructed resolution. -/
abbrev rightIso (n : ℕ) := (rightResolution S hS).isoRightDerivedObj T n

lemma map_f_eq (n : ℕ) :
    (T.rightDerived n).map S.f = (leftIso S hS T n).hom ≫
      homologyMap (imageSequence S hS T).f n ≫ (middleIso S hS T n).inv :=
  T.rightDerived_map_eq n S.f (resolutionF S hS) (augmentation_f S hS)

lemma map_g_eq (n : ℕ) :
    (T.rightDerived n).map S.g = (middleIso S hS T n).hom ≫
      homologyMap (imageSequence S hS T).g n ≫ (rightIso S hS T n).inv :=
  T.rightDerived_map_eq n S.g (resolutionG S hS) (augmentation_g S hS)

/-- The connecting map on the actual right-derived objects. -/
def δ (n : ℕ) : (T.rightDerived n).obj S.X₃ ⟶ (T.rightDerived (n + 1)).obj S.X₁ :=
  (rightIso S hS T n).hom ≫ (image_shortExact S hS T).δ n (n + 1) (by simp) ≫
    (leftIso S hS T (n + 1)).inv

@[reassoc (attr := simp)]
lemma map_g_δ (n : ℕ) : (T.rightDerived n).map S.g ≫ δ S hS T n = 0 := by
  rw [map_g_eq S hS T n]
  simp [δ, Category.assoc]

@[reassoc (attr := simp)]
lemma δ_map_f (n : ℕ) : δ S hS T n ≫ (T.rightDerived (n + 1)).map S.f = 0 := by
  rw [map_f_eq S hS T (n + 1)]
  simp [δ, Category.assoc]

include hS in
lemma map_f_map_g (n : ℕ) :
    (T.rightDerived n).map S.f ≫ (T.rightDerived n).map S.g = 0 := by
  rw [map_f_eq S hS T n, map_g_eq S hS T n]
  simp [Category.assoc, ← homologyMap_comp_assoc, (imageSequence S hS T).zero]

lemma exact_maps (n : ℕ) : (ShortComplex.mk _ _ (map_f_map_g S hS T n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ ((image_shortExact S hS T).homology_exact₂ n)
  exact (ShortComplex.isoMk (leftIso S hS T n) (middleIso S hS T n) (rightIso S hS T n)
    (by simp [map_f_eq S hS T n, Category.assoc])
    (by simp [map_g_eq S hS T n, Category.assoc])).symm

lemma exact_before_δ (n : ℕ) : (ShortComplex.mk _ _ (map_g_δ S hS T n)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    ((image_shortExact S hS T).homology_exact₃ n (n + 1) (by simp))
  exact (ShortComplex.isoMk
    (middleIso S hS T n) (rightIso S hS T n) (leftIso S hS T (n + 1))
    (by simp [map_g_eq S hS T n, Category.assoc])
    (by simp [δ, Category.assoc])).symm

lemma exact_after_δ (n : ℕ) : (ShortComplex.mk _ _ (δ_map_f S hS T n)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    ((image_shortExact S hS T).homology_exact₁ n (n + 1) (by simp))
  exact (ShortComplex.isoMk
    (rightIso S hS T n) (leftIso S hS T (n + 1)) (middleIso S hS T (n + 1))
    (by simp [δ, Category.assoc])
    (by simp [map_f_eq S hS T (n + 1), Category.assoc])).symm

/-- Acyclicity of the middle object makes each positive connecting map invertible. -/
lemma isIso_δ_succ (hT : ∀ n : ℕ, IsZero ((T.rightDerived (n + 1)).obj S.X₂))
    (n : ℕ) : IsIso (δ S hS T (n + 1)) := by
  have : Mono (δ S hS T (n + 1)) :=
    (exact_before_δ S hS T (n + 1)).mono_g ((hT n).eq_of_src _ _)
  have : Epi (δ S hS T (n + 1)) :=
    (exact_after_δ S hS T (n + 1)).epi_f ((hT (n + 1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- Positive dimension shifting, with the connecting map as its forward map. -/
def dimensionShift (hT : ∀ n : ℕ, IsZero ((T.rightDerived (n + 1)).obj S.X₂))
    (n : ℕ) : (T.rightDerived (n + 1)).obj S.X₃ ≅
      (T.rightDerived (n + 2)).obj S.X₁ :=
  have := isIso_δ_succ S hS T hT n
  asIso (δ S hS T (n + 1))

section Naturality

variable (R : ShortComplex C) (hR : R.ShortExact) (φ : S ⟶ R)

/-- Extend a row morphism across the compatible injective embeddings. -/
def rowLift : injectiveRow S ⟶ injectiveRow R :=
  let u := Injective.factorThru
    (φ.τ₂ ≫ (rowEmbedding R hR).τ₂ ≫ biprod.fst) (rowEmbedding S hS).τ₂
  let v := Injective.factorThru (φ.τ₃ ≫ (rowEmbedding R hR).τ₃)
    (rowEmbedding S hS).τ₃
  { τ₁ := biprod.inl ≫ u
    τ₂ := biprod.lift u (biprod.snd ≫ v)
    τ₃ := v
    comm₁₂ := by ext <;> simp
    comm₂₃ := by simp }

lemma rowLift_comm :
    rowEmbedding S hS ≫ rowLift S hS R hR φ = φ ≫ rowEmbedding R hR := by
  have h₂ : (rowEmbedding S hS ≫ rowLift S hS R hR φ).τ₂ =
      (φ ≫ rowEmbedding R hR).τ₂ := by
    apply biprod.hom_ext
    · simp [rowLift, Category.assoc]
    · simp [rowLift, Category.assoc, (rowEmbedding S hS).comm₂₃_assoc,
        (rowEmbedding R hR).comm₂₃, φ.comm₂₃_assoc]
  refine ShortComplex.hom_ext _ _ ?_ h₂ ?_
  · rw [← cancel_mono (injectiveRow R).f, ShortComplex.Hom.comm₁₂,
      ShortComplex.Hom.comm₁₂, h₂]
  · simp [rowLift]

/-- The induced morphisms of successive cokernel rows. -/
def syzygyMap : ∀ n, (syzygy S hS n).1 ⟶ (syzygy R hR n).1
  | 0 => φ
  | n + 1 => cokernel.map (inclusion S hS n) (inclusion R hR n) (syzygyMap n)
      (rowLift _ (syzygy S hS n).2 _ (syzygy R hR n).2 (syzygyMap n))
      (rowLift_comm _ _ _ _ _)

/-- A compatible comparison of the entire horseshoe diagrams. -/
def diagramMap : diagram S hS ⟶ diagram R hR :=
  CochainComplex.ofHom
    (fun n => rowLift _ (syzygy S hS n).2 _ (syzygy R hR n).2
      (syzygyMap S hS R hR φ n)) (fun n => by
        dsimp [diagram]
        rw [CochainComplex.of_d, CochainComplex.of_d]
        change _ ≫ (projection R hR n ≫ inclusion R hR (n + 1)) =
          (projection S hS n ≫ inclusion S hS (n + 1)) ≫ _
        rw [Category.assoc, rowLift_comm]
        simp [syzygyMap])

/-- The comparison of columns extends the original row morphism. -/
lemma column_comparison_comm (F : ShortComplex C ⥤ C) [F.PreservesZeroMorphisms] :
    (columnAugmentation S hS F).f 0 ≫
        ((F.mapHomologicalComplex _).map (diagramMap S hS R hR φ)).f 0 =
      F.map φ ≫ (columnAugmentation R hR F).f 0 := by
  rw [columnAugmentation_zero, columnAugmentation_zero]
  change F.map (rowEmbedding S hS) ≫ F.map (rowLift S hS R hR φ) =
    F.map φ ≫ F.map (rowEmbedding R hR)
  rw [← F.map_comp, ← F.map_comp, rowLift_comm]

/-- A morphism between the constructed short exact sequences of resolutions. -/
def comparison : resolutionSequence S hS ⟶ resolutionSequence R hR where
  τ₁ := (ShortComplex.π₁.mapHomologicalComplex _).map (diagramMap S hS R hR φ)
  τ₂ := (ShortComplex.π₂.mapHomologicalComplex _).map (diagramMap S hS R hR φ)
  τ₃ := (ShortComplex.π₃.mapHomologicalComplex _).map (diagramMap S hS R hR φ)
  comm₁₂ := (NatTrans.mapHomologicalComplex ShortComplex.π₁Toπ₂ _).naturality _
  comm₂₃ := (NatTrans.mapHomologicalComplex ShortComplex.π₂Toπ₃ _).naturality _

/-- Naturality of the connecting maps for every morphism of short exact sequences. -/
@[reassoc]
lemma δ_naturality (n : ℕ) :
    (T.rightDerived n).map φ.τ₃ ≫ δ R hR T n =
      δ S hS T n ≫ (T.rightDerived (n + 1)).map φ.τ₁ := by
  let ψ := comparison S hS R hR φ
  have h₁ : (leftResolution S hS).ι ≫ ψ.τ₁ =
      (CochainComplex.single₀ C).map φ.τ₁ ≫ (leftResolution R hR).ι := by
    exact InjectiveResolution.Hom.ι_comp_hom
      { hom := ψ.τ₁
        ι_f_zero_comp_hom_f_zero := by
          simp only [CochainComplex.single₀_map_f_zero]
          exact column_comparison_comm S hS R hR φ ShortComplex.π₁ }
  have h₃ : (rightResolution S hS).ι ≫ ψ.τ₃ =
      (CochainComplex.single₀ C).map φ.τ₃ ≫ (rightResolution R hR).ι := by
    exact InjectiveResolution.Hom.ι_comp_hom
      { hom := ψ.τ₃
        ι_f_zero_comp_hom_f_zero := by
          simp only [CochainComplex.single₀_map_f_zero]
          exact column_comparison_comm S hS R hR φ ShortComplex.π₃ }
  rw [T.rightDerived_map_eq n φ.τ₃ ψ.τ₃ h₃,
    T.rightDerived_map_eq (n + 1) φ.τ₁ ψ.τ₁ h₁]
  simp only [δ, Category.assoc, Iso.inv_hom_id_assoc]
  have H := HomologySequence.δ_naturality
    ((T.mapHomologicalComplex _).mapShortComplex.map ψ)
    (image_shortExact S hS T) (image_shortExact R hR T) n (n + 1) (by simp)
  dsimp only [Functor.mapShortComplex, Functor.comp_map, homologyFunctor] at H ⊢
  simpa only [Category.assoc] using congrArg
    (fun f => (rightIso S hS T n).hom ≫ f ≫ (leftIso R hR T (n + 1)).inv) H.symm

/-- The positive shift isomorphisms commute with coefficient morphisms. -/
lemma dimensionShift_naturality
    (hT : ∀ n : ℕ, IsZero ((T.rightDerived (n + 1)).obj S.X₂))
    (hTR : ∀ n : ℕ, IsZero ((T.rightDerived (n + 1)).obj R.X₂)) (n : ℕ) :
    (T.rightDerived (n + 1)).map φ.τ₃ ≫ (dimensionShift R hR T hTR n).hom =
      (dimensionShift S hS T hT n).hom ≫ (T.rightDerived (n + 2)).map φ.τ₁ :=
  δ_naturality S hS T R hR φ (n + 1)

end Naturality

variable [PreservesFiniteLimits T]

/-- The connecting map in degree zero starts at the original functor. -/
def δ₀ : T.obj S.X₃ ⟶ (T.rightDerived 1).obj S.X₁ :=
  T.toRightDerivedZero.app S.X₃ ≫ δ S hS T 0

omit [PreservesFiniteLimits T] in
@[reassoc (attr := simp)]
lemma map_g_δ₀ : T.map S.g ≫ δ₀ S hS T = 0 := by
  rw [δ₀, ← Category.assoc, T.toRightDerivedZero.naturality, Category.assoc,
    map_g_δ, comp_zero]

lemma exact_before_δ₀ : (ShortComplex.mk _ _ (map_g_δ₀ S hS T)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (exact_before_δ S hS T 0)
  exact (ShortComplex.isoMk
    (S₁ := ShortComplex.mk _ _ (map_g_δ₀ S hS T))
    (S₂ := ShortComplex.mk _ _ (map_g_δ S hS T 0))
    (T.rightDerivedZeroIsoSelf.app S.X₂).symm
    (T.rightDerivedZeroIsoSelf.app S.X₃).symm (Iso.refl _)
    (T.toRightDerivedZero.naturality S.g).symm
    (by simp [δ₀])).symm

include hS in
omit [EnoughInjectives C] in
/-- Left exactness supplies exactness at the initial middle object. -/
lemma exact_zero_maps : (S.map T).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (KernelFork.mapIsLimit _ hS.fIsKernel T)

include hS in
omit [Abelian D] [EnoughInjectives C] [T.Additive] in
/-- The initial arrow is monomorphic. -/
lemma mono_zero_map : Mono (T.map S.f) := by
  have := hS.mono_f
  infer_instance

omit [PreservesFiniteLimits T] in
@[reassoc (attr := simp)]
lemma δ₀_map_f : δ₀ S hS T ≫ (T.rightDerived 1).map S.f = 0 := by
  simp [δ₀, Category.assoc]

/-- Exactness at the first positive derived object. -/
lemma exact_after_δ₀ : (ShortComplex.mk _ _ (δ₀_map_f S hS T)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (exact_after_δ S hS T 0)
  exact (ShortComplex.isoMk
    (S₁ := ShortComplex.mk _ _ (δ₀_map_f S hS T))
    (S₂ := ShortComplex.mk _ _ (δ_map_f S hS T 0))
    (T.rightDerivedZeroIsoSelf.app S.X₃).symm (Iso.refl _) (Iso.refl _)
    (by simp [δ₀]) (by simp)).symm

omit [PreservesFiniteLimits T] in
/-- The degree-zero connecting map is natural in short exact sequences. -/
@[reassoc]
lemma δ₀_naturality (R : ShortComplex C) (hR : R.ShortExact) (φ : S ⟶ R) :
    T.map φ.τ₃ ≫ δ₀ R hR T = δ₀ S hS T ≫ (T.rightDerived 1).map φ.τ₁ := by
  dsimp only [δ₀]
  rw [← Category.assoc, T.toRightDerivedZero.naturality, Category.assoc,
    δ_naturality S hS T R hR φ 0]
  simp only [Category.assoc]

end FLT.Mazur.RightDerivedDimensionShift

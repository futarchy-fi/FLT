/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# The injective horseshoe construction

A short exact sequence embeds in a split short exact sequence of injectives.
The cokernel sequence is again short exact. Iteration constructs three injective
resolutions, with compatible augmentations and a degreewise split short exact
sequence of cochain complexes. Only the original short exact sequence is an input.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe v u

namespace FLT.Mazur.InjectiveHorseshoe

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  (S : ShortComplex C) (hS : S.ShortExact)

/-- The split injective row into which the original sequence embeds. -/
abbrev injectiveRow : ShortComplex C :=
  ShortComplex.mk (biprod.inl : Injective.under S.X₁ ⟶
    Injective.under S.X₁ ⊞ Injective.under S.X₃) biprod.snd (by simp)

/-- The canonical splitting of the injective row. -/
def rowSplitting : (injectiveRow S).Splitting :=
  ShortComplex.Splitting.ofHasBinaryBiproduct _ _

instance injectiveRow₁ : Injective (injectiveRow S).X₁ := inferInstance
instance injectiveRow₂ : Injective (injectiveRow S).X₂ := inferInstance
instance injectiveRow₃ : Injective (injectiveRow S).X₃ := inferInstance

/-- Extend the left injection across the original monomorphism. -/
def rowEmbedding : S ⟶ injectiveRow S := by
  have := hS.mono_f
  exact
    { τ₁ := Injective.ι S.X₁
      τ₂ := biprod.lift (Injective.factorThru (Injective.ι S.X₁) S.f)
        (S.g ≫ Injective.ι S.X₃)
      τ₃ := Injective.ι S.X₃
      comm₁₂ := by ext <;> simp [Category.assoc]
      comm₂₃ := by simp }

instance rowEmbedding_mono₁ : Mono (rowEmbedding S hS).τ₁ := by
  dsimp [rowEmbedding]
  infer_instance

instance rowEmbedding_mono₃ : Mono (rowEmbedding S hS).τ₃ := by
  dsimp [rowEmbedding]
  infer_instance

instance rowEmbedding_mono₂ : Mono (rowEmbedding S hS).τ₂ := by
  have := hS.mono_f
  exact ShortComplex.mono_τ₂_of_exact_of_mono _ hS.exact

/-- The snake diagram for the compatible embedding. -/
def quotientSnake : ShortComplex.SnakeInput C where
  L₀ := kernel (rowEmbedding S hS)
  L₁ := S
  L₂ := injectiveRow S
  L₃ := cokernel (rowEmbedding S hS)
  v₀₁ := kernel.ι (rowEmbedding S hS)
  v₁₂ := rowEmbedding S hS
  v₂₃ := cokernel.π (rowEmbedding S hS)
  h₀ := kernelIsKernel _
  h₃ := cokernelIsCokernel _
  L₁_exact := hS.exact
  epi_L₁_g := hS.epi_g
  L₂_exact := (rowSplitting S).exact
  mono_L₂_f := (rowSplitting S).shortExact.mono_f

/-- The quotient of the embedding is another short exact sequence. -/
lemma quotient_shortExact : (cokernel (rowEmbedding S hS)).ShortExact := by
  let D := quotientSnake S hS
  have : Mono D.v₁₂.τ₃ := rowEmbedding_mono₃ S hS
  have : Epi D.L₂.g := (rowSplitting S).shortExact.epi_g
  have hzero : IsZero D.L₀.X₃ := KernelFork.IsLimit.isZero_of_mono D.h₀τ₃
  have hδ : D.δ = 0 := hzero.eq_of_src _ _
  exact
    { exact := D.L₃_exact
      mono_f := (D.L₂'.exact_iff_mono hδ).1 D.L₂'_exact
      epi_g := D.epi_L₃_g }

/-- Successive cokernel rows, including the original row in degree zero. -/
def syzygy : ℕ → { R : ShortComplex C // R.ShortExact }
  | 0 => ⟨S, hS⟩
  | n + 1 => ⟨cokernel (rowEmbedding (syzygy n).1 (syzygy n).2),
      quotient_shortExact (syzygy n).1 (syzygy n).2⟩

/-- The split row in degree `n`. -/
abbrev term (n : ℕ) : ShortComplex C := injectiveRow (syzygy S hS n).1

/-- The embedding of each syzygy row. -/
abbrev inclusion (n : ℕ) : (syzygy S hS n).1 ⟶ term S hS n :=
  rowEmbedding _ (syzygy S hS n).2

/-- The projection onto the next syzygy row. -/
abbrev projection (n : ℕ) : term S hS n ⟶ (syzygy S hS (n + 1)).1 :=
  cokernel.π (inclusion S hS n)

/-- The differential of the diagram of resolutions. -/
def differential (n : ℕ) : term S hS n ⟶ term S hS (n + 1) :=
  projection S hS n ≫ inclusion S hS (n + 1)

lemma differential_comp (n : ℕ) :
    differential S hS n ≫ differential S hS (n + 1) = 0 := by
  simp [differential, Category.assoc]

/-- The cochain complex of split short exact rows. -/
def diagram : CochainComplex (ShortComplex C) ℕ :=
  CochainComplex.of (term S hS) (differential S hS) (differential_comp S hS)

section Column

variable (F : ShortComplex C ⥤ C) [F.PreservesZeroMorphisms]

/-- A column of the diagram. -/
def column : CochainComplex C ℕ :=
  (F.mapHomologicalComplex _).obj (diagram S hS)

@[simp]
lemma column_d (n : ℕ) :
    (column S hS F).d n (n + 1) = F.map (differential S hS n) := by
  simp [column, diagram, CochainComplex.of_d]

lemma column_inclusion_projection (n : ℕ) :
    F.map (inclusion S hS n) ≫ F.map (projection S hS n) = 0 := by
  rw [← F.map_comp, cokernel.condition, F.map_zero]

variable [PreservesFiniteColimits F]

lemma column_exact (n : ℕ) :
    (ShortComplex.mk _ _ (column_inclusion_projection S hS F n)).Exact :=
  ShortComplex.exact_of_g_is_cokernel _
    (CokernelCofork.mapIsColimit _ (cokernelIsCokernel _) F)

omit [PreservesFiniteColimits F] in
lemma column_inclusion_d (n : ℕ) :
    F.map (inclusion S hS n) ≫ F.map (differential S hS n) = 0 := by
  rw [differential, F.map_comp, ← Category.assoc,
    column_inclusion_projection, zero_comp]

variable (hm : ∀ n, Mono (F.map (inclusion S hS n)))

include hm in
lemma column_exact_d (n : ℕ) :
    (ShortComplex.mk (F.map (inclusion S hS n))
      (F.map (differential S hS n)) (column_inclusion_d S hS F n)).Exact := by
  let φ : ShortComplex.mk _ _ (column_inclusion_projection S hS F n) ⟶
      ShortComplex.mk (F.map (inclusion S hS n)) (F.map (differential S hS n))
        (column_inclusion_d S hS F n) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := F.map (inclusion S hS (n + 1))
      comm₂₃ := by simp [differential] }
  have := hm (n + 1)
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 (column_exact S hS F n)

include hm in
lemma column_exact_succ (n : ℕ) : (column S hS F).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  let φ : (column S hS F).sc' n (n + 1) (n + 2) ⟶
      ShortComplex.mk (F.map (inclusion S hS (n + 1)))
        (F.map (differential S hS (n + 1))) (column_inclusion_d S hS F (n + 1)) :=
    { τ₁ := F.map (projection S hS n)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [differential]
      comm₂₃ := by simp }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
    (column_exact_d S hS F hm (n + 1))

/-- The column augmentation comes from the original row embedding. -/
def columnAugmentation : (CochainComplex.single₀ C).obj (F.obj S) ⟶ column S hS F :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨F.map (inclusion S hS 0), by
      rw [column_d]; exact column_inclusion_d S hS F 0⟩

omit [PreservesFiniteColimits F] in
@[simp]
lemma columnAugmentation_zero :
    (columnAugmentation S hS F).f 0 = F.map (inclusion S hS 0) := by
  simp [columnAugmentation]

include hm in
lemma columnAugmentation_quasiIso : QuasiIso (columnAugmentation S hS F) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · have := hm 0
      refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
        ⟨column_exact_d S hS F hm 0, inferInstance⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simp)
    all_goals simp
  | succ n =>
    rw [quasiIsoAt_iff_exactAt _ _
      (CochainComplex.exactAt_succ_single_obj _ _)]
    exact column_exact_succ S hS F hm n

/-- Construct a resolution from a column of the internally built diagram. -/
def columnResolution (hi : ∀ n, Injective (F.obj (term S hS n))) :
    InjectiveResolution (F.obj S) where
  cocomplex := column S hS F
  injective := hi
  ι := columnAugmentation S hS F
  quasiIso := columnAugmentation_quasiIso S hS F hm

end Column

/-- The constructed resolution of the left object. -/
def leftResolution : InjectiveResolution S.X₁ :=
  columnResolution S hS ShortComplex.π₁ (fun n => rowEmbedding_mono₁ _ (syzygy S hS n).2)
    (fun _ => injectiveRow₁ _)

/-- The constructed resolution of the middle object. -/
def middleResolution : InjectiveResolution S.X₂ :=
  columnResolution S hS ShortComplex.π₂ (fun n => rowEmbedding_mono₂ _ (syzygy S hS n).2)
    (fun _ => injectiveRow₂ _)

/-- The constructed resolution of the right object. -/
def rightResolution : InjectiveResolution S.X₃ :=
  columnResolution S hS ShortComplex.π₃ (fun n => rowEmbedding_mono₃ _ (syzygy S hS n).2)
    (fun _ => injectiveRow₃ _)

/-- The first map between the constructed resolutions. -/
def resolutionF : (leftResolution S hS).cocomplex ⟶ (middleResolution S hS).cocomplex :=
  (NatTrans.mapHomologicalComplex ShortComplex.π₁Toπ₂ _).app (diagram S hS)

/-- The second map between the constructed resolutions. -/
def resolutionG : (middleResolution S hS).cocomplex ⟶ (rightResolution S hS).cocomplex :=
  (NatTrans.mapHomologicalComplex ShortComplex.π₂Toπ₃ _).app (diagram S hS)

lemma resolutionF_comp_resolutionG : resolutionF S hS ≫ resolutionG S hS = 0 := by
  ext n
  exact (term S hS n).zero

/-- The short complex of compatible injective resolutions. -/
def resolutionSequence : ShortComplex (CochainComplex C ℕ) :=
  ShortComplex.mk _ _ (resolutionF_comp_resolutionG S hS)

/-- Each degree of the resolution sequence is split exact. -/
def degreeSplitting (n : ℕ) :
    ((resolutionSequence S hS).map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).Splitting :=
  rowSplitting (syzygy S hS n).1

lemma resolutionSequence_shortExact : (resolutionSequence S hS).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (degreeSplitting S hS n).shortExact)

/-- The first map extends the original injection. -/
def resolutionFHom : (leftResolution S hS).Hom (middleResolution S hS) S.f where
  hom := resolutionF S hS
  ι_f_zero_comp_hom_f_zero := by
    simp only [CochainComplex.single₀_map_f_zero]
    change (columnAugmentation S hS ShortComplex.π₁).f 0 ≫ (term S hS 0).f =
      S.f ≫ (columnAugmentation S hS ShortComplex.π₂).f 0
    rw [columnAugmentation_zero, columnAugmentation_zero]
    exact (inclusion S hS 0).comm₁₂

/-- The second map extends the original surjection. -/
def resolutionGHom : (middleResolution S hS).Hom (rightResolution S hS) S.g where
  hom := resolutionG S hS
  ι_f_zero_comp_hom_f_zero := by
    simp only [CochainComplex.single₀_map_f_zero]
    change (columnAugmentation S hS ShortComplex.π₂).f 0 ≫ (term S hS 0).g =
      S.g ≫ (columnAugmentation S hS ShortComplex.π₃).f 0
    rw [columnAugmentation_zero, columnAugmentation_zero]
    exact (inclusion S hS 0).comm₂₃

/-- Compatibility of the first augmentation square. -/
@[reassoc]
lemma augmentation_f :
    (leftResolution S hS).ι ≫ resolutionF S hS =
      (CochainComplex.single₀ C).map S.f ≫ (middleResolution S hS).ι :=
  (resolutionFHom S hS).ι_comp_hom

/-- Compatibility of the second augmentation square. -/
@[reassoc]
lemma augmentation_g :
    (middleResolution S hS).ι ≫ resolutionG S hS =
      (CochainComplex.single₀ C).map S.g ≫ (rightResolution S hS).ι :=
  (resolutionGHom S hS).ι_comp_hom

end FLT.Mazur.InjectiveHorseshoe

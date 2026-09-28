/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizationCechCompare

/-!
# Exactness of finite principal-open Čech covers

Inside `D(f i)`, inserting `i` contracts the restricted complex. Finite-product
localization transports this contraction to prove exactness on a spanning cover.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite PrimeSpectrum

universe u

namespace FLT.Mazur.LocalizationCechExact

open TildePrincipalOpen LocalizationCech LocalizationCechCompare

variable {R : CommRingCat.{u}} {ι : Type u} (f : ι → R) (M : ModuleCat.{u} R)
variable (i : ι)

/-- Inserting a base member does not shrink the intersection. -/
lemma baseSplit_open_le {q : ℕ} (s : Fin (q + 1) → ι) :
    basicOpen (f i * ∏ j, f (s j)) ≤
      basicOpen (f i * ∏ j : Fin (q + 2), f (Fin.cons (α := fun _ ↦ ι) i s j)) := by
  conv_rhs => rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, basicOpen_mul]
  exact le_inf inf_le_left (le_inf inf_le_left inf_le_right)

/-- Insertion of the base index on tuple sections, lowering Čech degree by one. -/
def baseSplitHomotopy (q : ℕ) : (baseComplex f M (f i)).X (q + 1) ⟶ (baseComplex f M (f i)).X q :=
  ModuleCat.ofHom
    { toFun := fun x s ↦
        ((modulesSpecToSheaf.obj (tilde M)).presheaf.map
          (homOfLE (baseSplit_open_le f i s)).op).hom (x (Fin.cons (α := fun _ ↦ ι) i s))
      map_add' := fun x y ↦ funext fun s ↦ map_add _ (x (Fin.cons i s)) (y (Fin.cons i s))
      map_smul' := fun r x ↦ funext fun s ↦ map_smul _ r (x (Fin.cons i s)) }

/-- The first coface cancels insertion. -/
lemma baseSplit_coface_zero (q : ℕ) :
    baseReindex f M (f i) (0 : Fin (q + 2)).succAbove ≫ baseSplitHomotopy f M i q = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext s
  change (((modulesSpecToSheaf.obj (tilde M)).presheaf.map _) ≫
    ((modulesSpecToSheaf.obj (tilde M)).presheaf.map _)).hom _ = x s
  rw [← Functor.map_comp]
  change ((modulesSpecToSheaf.obj (tilde M)).presheaf.map (𝟙 _)).hom (x s) = x s
  simp

private lemma baseSplit_restrict_eq {p : ℕ} (x : baseTerm f M (f i) p)
    {s t : Fin (p + 1) → ι} {U : TopologicalSpace.Opens (PrimeSpectrum R)}
    (hs : U ≤ basicOpen (f i * ∏ j, f (s j))) (ht : U ≤ basicOpen (f i * ∏ j, f (t j)))
    (h : s = t) :
    ((modulesSpecToSheaf.obj (tilde M)).presheaf.map (homOfLE hs).op).hom (x s) =
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.map (homOfLE ht).op).hom (x t) := by
  subst t
  rfl

/-- All remaining cofaces commute with insertion after shifting their index. -/
lemma baseSplit_coface_succ (q : ℕ) (j : Fin (q + 2)) :
    baseReindex f M (f i) j.succ.succAbove ≫ baseSplitHomotopy f M i (q + 1) =
      baseSplitHomotopy f M i q ≫ baseReindex f M (f i) j.succAbove := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext s
  change (((modulesSpecToSheaf.obj (tilde M)).presheaf.map _) ≫
    ((modulesSpecToSheaf.obj (tilde M)).presheaf.map _)).hom
      (x (Fin.cons (α := fun _ ↦ ι) i s ∘ j.succ.succAbove)) =
    (((modulesSpecToSheaf.obj (tilde M)).presheaf.map _) ≫
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.map _)).hom
        (x (Fin.cons (α := fun _ ↦ ι) i (s ∘ j.succAbove)))
  simp only [← Functor.map_comp]
  exact baseSplit_restrict_eq f M i x _ _ (Fin.cons_comp_succ_succAbove i s j)

/-- The contraction identity in positive Čech degrees. -/
lemma baseSplit_homotopy_identity (q : ℕ) :
    (baseComplex f M (f i)).d (q + 1) (q + 2) ≫ baseSplitHomotopy f M i (q + 1) +
      baseSplitHomotopy f M i q ≫ (baseComplex f M (f i)).d q (q + 1) = 𝟙 _ := by
  simp only [baseDifferential, Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul, baseSplit_coface_zero,
    baseSplit_coface_succ, Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
    Finset.sum_neg_distrib]
  abel

/-- The singleton base member is the base open. -/
lemma baseSplit_point_open :
    basicOpen (f i) ≤ basicOpen (f i * ∏ _ : Fin 1, f i) := by
  rw [Fin.prod_univ_one, basicOpen_mul]
  exact le_inf le_rfl le_rfl

/-- The contraction from Čech degree zero to the augmented coefficient term. -/
def baseSplitRetraction : baseTerm f M (f i) 0 ⟶ sections M (f i) :=
  ModuleCat.ofHom (LinearMap.proj (fun _ : Fin 1 ↦ i)) ≫
    (modulesSpecToSheaf.obj (tilde M)).presheaf.map
      (homOfLE (baseSplit_point_open f i)).op

/-- The last coface in degree zero factors through coefficients. -/
lemma baseSplit_coface_one :
    baseReindex f M (f i) (1 : Fin 2).succAbove ≫ baseSplitHomotopy f M i 0 =
      baseSplitRetraction f M i ≫ baseAugment f M (f i) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext s
  change (((modulesSpecToSheaf.obj (tilde M)).presheaf.map _) ≫
    ((modulesSpecToSheaf.obj (tilde M)).presheaf.map _)).hom
      (x (Fin.cons (α := fun _ ↦ ι) i s ∘ (1 : Fin 2).succAbove)) =
    (restriction M (f i) (∏ j, f (s j))) ((baseSplitRetraction f M i).hom x)
  change _ = (((modulesSpecToSheaf.obj (tilde M)).presheaf.map
    (homOfLE (baseSplit_point_open f i)).op) ≫
    ((modulesSpecToSheaf.obj (tilde M)).presheaf.map
      (homOfLE (basicOpen_mul_le_left (f i) (∏ j, f (s j)))).op)).hom (x (fun _ ↦ i))
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply baseSplit_restrict_eq
  ext j
  fin_cases j
  rfl

/-- The contraction identity in Čech degree zero includes the augmentation. -/
lemma baseSplit_homotopy_zero :
    (baseComplex f M (f i)).d 0 1 ≫ baseSplitHomotopy f M i 0 +
      (baseSplitRetraction f M i ≫ baseAugment f M (f i) :
        (baseComplex f M (f i)).X 0 ⟶ (baseComplex f M (f i)).X 0) = 𝟙 _ := by
  rw [baseDifferential, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one,
    neg_one_zsmul, Preadditive.add_comp, Preadditive.neg_comp,
    baseSplit_coface_zero, baseSplit_coface_one]
  abel

private lemma baseSplit_exact {A B C : ModuleCat.{u} R}
    (a : A ⟶ B) (b : B ⟶ C) (r : B ⟶ A) (s : C ⟶ B)
    (hab : a ≫ b = 0) (h : b ≫ s + r ≫ a = 𝟙 B) :
    Function.Exact a.hom b.hom := by
  intro x
  constructor
  · intro hx
    refine ⟨r.hom x, ?_⟩
    have hh := congrArg (fun t ↦ t.hom x) h
    simpa only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply, hx, map_zero, zero_add, ModuleCat.hom_id,
      LinearMap.id_apply] using hh
  · rintro ⟨y, rfl⟩
    exact congrArg (fun t ↦ t.hom y) hab

/-- The unaugmented Čech complex is exact in every positive degree. -/
lemma baseSplit_exactAt_succ (q : ℕ) : (baseComplex f M (f i)).ExactAt (q + 1) := by
  rw [(baseComplex f M (f i)).exactAt_iff' q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact baseSplit_exact _ _ (baseSplitHomotopy f M i q) (baseSplitHomotopy f M i (q + 1))
    ((baseComplex f M (f i)).d_comp_d _ _ _) (baseSplit_homotopy_identity f M i q)


variable [Finite ι] (hf : Ideal.span (Set.range f) = ⊤)

include hf

/-- Exactness in all positive Čech degrees for a finite spanning principal cover. -/
lemma exactAt_succ (q : ℕ) : (complex f M).ExactAt (q + 1) := by
  apply (exactAt_iff_sections f hf _ _).mpr
  intro i
  exact (baseSplit_exactAt_succ f M i q).of_iso (complexIso f M (f i)).symm

set_option maxHeartbeats 800000 in
-- Unifying the localized section modules across the comparison is expensive.
/-- The augmentation has precisely the degree-zero cocycles as its image. -/
lemma augment_exact : Function.Exact (augment f M).hom ((complex f M).d 0 1).hom := by
  apply (exact_iff_sections f hf _ _).mpr
  intro i
  apply (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := LinearEquiv.refl R (sections M (f i)))
    (e₂ := compare f M (f i) 0) (e₃ := compare f M (f i) 1)
    (g₁₂ := (baseAugment f M (f i)).hom)
    (g₂₃ := ((baseComplex f M (f i)).d 0 1).hom)
    (by simpa using (compare_augment f M (f i)).symm)
    (congrArg ModuleCat.Hom.hom (compare_differential f M (f i) 0)).symm).mp
  exact baseSplit_exact _ _ (baseSplitRetraction f M i) (baseSplitHomotopy f M i 0)
    (baseAugment_d f M (f i)) (baseSplit_homotopy_zero f M i)

/-- The augmented principal-open Čech complex is exact in every degree. -/
lemma augmented_exactAt (q : ℕ) : (augmentedComplex f M).ExactAt q := by
  cases q with
  | zero => exact augmentedComplex_exactAt_zero f M hf
  | succ q =>
    rw [(augmentedComplex f M).exactAt_iff' q (q + 1) (q + 2) (by simp) (by simp)]
    cases q with
    | zero =>
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
        (augment_exact f M hf)
    | succ q =>
      exact ((complex f M).exactAt_iff' q (q + 1) (q + 2) (by simp) (by simp)).mp
        (exactAt_succ f M hf q)

/-- Positive-degree Čech cohomology vanishes on a finite spanning principal cover. -/
lemma isZero_homology (q : ℕ) : Limits.IsZero ((complex f M).homology (q + 1)) :=
  (exactAt_succ f M hf q).isZero_homology

/-- The augmentation identifies the coefficient module with degree-zero cocycles. -/
def cyclesIso : M ≅ (complex f M).cycles 0 := by
  let S := ShortComplex.mk (augment f M) ((complex f M).d 0 1) (augment_d f M)
  have hS : S.Exact :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr (augment_exact f M hf)
  have : Mono S.f := (ModuleCat.mono_iff_injective _).mpr (augment_injective f M hf)
  exact Limits.IsLimit.conePointUniqueUpToIso hS.fIsKernel
    ((complex f M).cyclesIsKernel 0 1 (by simp))

/-- Degree-zero Čech cohomology is the coefficient module. -/
def homologyZeroIso : M ≅ (complex f M).homology 0 :=
  cyclesIso f M hf ≪≫ (complex f M).isoHomologyπ₀

/-- The degree-zero identification is induced by the original augmentation. -/
lemma homologyZeroIso_augmentation :
    (homologyZeroIso f M hf).hom =
      (complex f M).liftCycles (i := 0) (augment f M) 1 (by simp) (augment_d f M) ≫
        (complex f M).homologyπ 0 := by
  change (cyclesIso f M hf).hom ≫ _ = _
  congr 1
  apply (cancel_mono ((complex f M).iCycles 0)).mp
  simp only [HomologicalComplex.liftCycles_i]
  exact Limits.IsLimit.conePointUniqueUpToIso_hom_comp _ _
    (Limits.WalkingParallelPair.zero)

end FLT.Mazur.LocalizationCechExact

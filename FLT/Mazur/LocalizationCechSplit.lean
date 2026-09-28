/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizationCech

/-!
# Contraction for a split principal-open cover

Inserting an index whose defining function is a unit contracts the augmented
Čech complex. The construction works for arbitrary index types and rings.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite PrimeSpectrum

universe u

namespace FLT.Mazur.LocalizationCech

open TildePrincipalOpen

variable {R : CommRingCat.{u}} {ι : Type u} (f : ι → R) (M : ModuleCat.{u} R)
variable (i : ι) (hi : IsUnit (f i))

include hi in
/-- Inserting a unit member does not shrink the intersection. -/
lemma split_open_le {q : ℕ} (s : Fin (q + 1) → ι) :
    basicOpen (∏ j, f (s j)) ≤
      basicOpen (∏ j : Fin (q + 2), f (Fin.cons (α := fun _ ↦ ι) i s j)) := by
  conv_rhs => rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, basicOpen_mul]
  exact le_inf (fun x _ ↦ x.asIdeal.notMem_of_isUnit hi) le_rfl

/-- Insertion of the unit index on tuple sections, lowering Čech degree by one. -/
def splitHomotopy (q : ℕ) : (complex f M).X (q + 1) ⟶ (complex f M).X q :=
  ModuleCat.ofHom
    { toFun := fun x s ↦
        ((modulesSpecToSheaf.obj (tilde M)).presheaf.map
          (homOfLE (split_open_le f i hi s)).op).hom (x (Fin.cons (α := fun _ ↦ ι) i s))
      map_add' := fun x y ↦ funext fun s ↦ map_add _ (x (Fin.cons i s)) (y (Fin.cons i s))
      map_smul' := fun r x ↦ funext fun s ↦ map_smul _ r (x (Fin.cons i s)) }

/-- The first coface cancels insertion. -/
lemma split_coface_zero (q : ℕ) :
    reindex f M (0 : Fin (q + 2)).succAbove ≫ splitHomotopy f M i hi q = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext s
  change (((modulesSpecToSheaf.obj (tilde M)).presheaf.map _) ≫
    ((modulesSpecToSheaf.obj (tilde M)).presheaf.map _)).hom _ = x s
  rw [← Functor.map_comp]
  change ((modulesSpecToSheaf.obj (tilde M)).presheaf.map (𝟙 _)).hom (x s) = x s
  simp

private lemma split_restrict_eq {p : ℕ} (x : term f M p)
    {s t : Fin (p + 1) → ι} {U : TopologicalSpace.Opens (PrimeSpectrum R)}
    (hs : U ≤ basicOpen (∏ j, f (s j))) (ht : U ≤ basicOpen (∏ j, f (t j)))
    (h : s = t) :
    ((modulesSpecToSheaf.obj (tilde M)).presheaf.map (homOfLE hs).op).hom (x s) =
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.map (homOfLE ht).op).hom (x t) := by
  subst t
  rfl

/-- All remaining cofaces commute with insertion after shifting their index. -/
lemma split_coface_succ (q : ℕ) (j : Fin (q + 2)) :
    reindex f M j.succ.succAbove ≫ splitHomotopy f M i hi (q + 1) =
      splitHomotopy f M i hi q ≫ reindex f M j.succAbove := by
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
  exact split_restrict_eq f M x _ _ (Fin.cons_comp_succ_succAbove i s j)

/-- The contraction identity in positive Čech degrees. -/
lemma split_homotopy_identity (q : ℕ) :
    (complex f M).d (q + 1) (q + 2) ≫ splitHomotopy f M i hi (q + 1) +
      splitHomotopy f M i hi q ≫ (complex f M).d q (q + 1) = 𝟙 _ := by
  simp only [differential, Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul, split_coface_zero,
    split_coface_succ, Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
    Finset.sum_neg_distrib]
  abel

include hi in
/-- The singleton unit member is the whole spectrum. -/
lemma split_point_open :
    (⊤ : TopologicalSpace.Opens (PrimeSpectrum R)) ≤ basicOpen (∏ _ : Fin 1, f i) := by
  rw [Fin.prod_univ_one]
  exact fun x _ ↦ x.asIdeal.notMem_of_isUnit hi

/-- The contraction from Čech degree zero to the augmented coefficient term. -/
def splitRetraction : term f M 0 ⟶ M :=
  ModuleCat.ofHom (LinearMap.proj (fun _ : Fin 1 ↦ i)) ≫
    (modulesSpecToSheaf.obj (tilde M)).presheaf.map
      (homOfLE (split_point_open f i hi)).op ≫ (tilde.isoTop M).inv

/-- The augmentation followed by the contraction is the identity on coefficients. -/
lemma split_augment_retraction : augment f M ≫ splitRetraction f M i hi = 𝟙 M := by
  change (tilde.toOpen M _ ≫
    (modulesSpecToSheaf.obj (tilde M)).presheaf.map _) ≫ (tilde.isoTop M).inv = _
  rw [tilde.toOpen_res]
  exact (tilde.isoTop M).hom_inv_id

private lemma split_retraction_toOpen (U : TopologicalSpace.Opens (PrimeSpectrum R))
    (x : term f M 0) :
    (tilde.toOpen M U).hom ((splitRetraction f M i hi).hom x) =
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.map
        (homOfLE (le_top.trans (split_point_open f i hi))).op).hom (x (fun _ ↦ i)) := by
  change (_ ≫ (tilde.isoTop M).inv ≫ tilde.toOpen M U).hom (x (fun _ ↦ i)) = _
  rw [← tilde.toOpen_res M ⊤ U (homOfLE le_top)]
  change (_ ≫ (tilde.isoTop M).inv ≫ (tilde.isoTop M).hom ≫ _).hom _ = _
  rw [Iso.inv_hom_id_assoc, ← Functor.map_comp]
  rfl

/-- The last coface in degree zero factors through coefficients. -/
lemma split_coface_one :
    reindex f M (1 : Fin 2).succAbove ≫ splitHomotopy f M i hi 0 =
      splitRetraction f M i hi ≫ augment f M := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext s
  change (((modulesSpecToSheaf.obj (tilde M)).presheaf.map _) ≫
    ((modulesSpecToSheaf.obj (tilde M)).presheaf.map _)).hom
      (x (Fin.cons (α := fun _ ↦ ι) i s ∘ (1 : Fin 2).succAbove)) =
    (tilde.toOpen M (basicOpen (∏ j, f (s j)))).hom ((splitRetraction f M i hi).hom x)
  rw [split_retraction_toOpen, ← Functor.map_comp]
  apply split_restrict_eq
  ext j
  fin_cases j
  rfl

/-- The contraction identity in Čech degree zero includes the augmentation. -/
lemma split_homotopy_zero :
    (complex f M).d 0 1 ≫ splitHomotopy f M i hi 0 +
      (splitRetraction f M i hi ≫ augment f M : (complex f M).X 0 ⟶ (complex f M).X 0) = 𝟙 _ := by
  rw [differential, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one,
    neg_one_zsmul, Preadditive.add_comp, Preadditive.neg_comp,
    split_coface_zero, split_coface_one]
  abel

private lemma split_exact {A B C : ModuleCat.{u} R}
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

include hi in
/-- The unaugmented Čech complex is exact in every positive degree. -/
lemma split_exactAt_succ (q : ℕ) : (complex f M).ExactAt (q + 1) := by
  rw [(complex f M).exactAt_iff' q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact split_exact _ _ (splitHomotopy f M i hi q) (splitHomotopy f M i hi (q + 1))
    ((complex f M).d_comp_d _ _ _) (split_homotopy_identity f M i hi q)

include hi in
/-- The augmented principal-open complex is exact in every degree for a unit member. -/
lemma split_augmented_exactAt (q : ℕ) : (augmentedComplex f M).ExactAt q := by
  cases q with
  | zero =>
    apply augmentedComplex_exactAt_zero f M
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_range_self i)) hi
  | succ q =>
    rw [(augmentedComplex f M).exactAt_iff' q (q + 1) (q + 2) (by simp) (by simp),
      ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    cases q with
    | zero =>
      exact split_exact _ _ (splitRetraction f M i hi) (splitHomotopy f M i hi 0)
        (augment_d f M) (split_homotopy_zero f M i hi)
    | succ q =>
      exact split_exact _ _ (splitHomotopy f M i hi q) (splitHomotopy f M i hi (q + 1))
        ((complex f M).d_comp_d _ _ _) (split_homotopy_identity f M i hi q)

include hi in
/-- Positive Čech cohomology vanishes for a split principal cover. -/
lemma split_isZero_homology (q : ℕ) :
    Limits.IsZero ((complex f M).homology (q + 1)) :=
  (split_exactAt_succ f M i hi q).isZero_homology

/-- The augmentation identifies coefficients with degree-zero cocycles. -/
def splitCyclesIso : M ≅ (complex f M).cycles 0 where
  hom := (complex f M).liftCycles (i := 0) (augment f M) 1 (by simp) (augment_d f M)
  inv := (complex f M).iCycles 0 ≫ splitRetraction f M i hi
  hom_inv_id := by
    rw [← Category.assoc, HomologicalComplex.liftCycles_i, split_augment_retraction]
  inv_hom_id := by
    apply (cancel_mono ((complex f M).iCycles 0)).mp
    simp only [Category.assoc, HomologicalComplex.liftCycles_i, Category.id_comp]
    have h := congrArg (fun a ↦ (complex f M).iCycles 0 ≫ a)
      (split_homotopy_zero f M i hi)
    simpa only [Preadditive.comp_add, ← Category.assoc,
      HomologicalComplex.iCycles_d, Limits.zero_comp, zero_add, Category.comp_id] using h

/-- Degree-zero Čech cohomology is the coefficient module via the augmentation. -/
def splitHomologyZeroIso : M ≅ (complex f M).homology 0 :=
  splitCyclesIso f M i hi ≪≫ (complex f M).isoHomologyπ₀

/-- The degree-zero comparison is induced by the original augmentation. -/
lemma splitHomologyZeroIso_augmentation :
    (splitHomologyZeroIso f M i hi).hom =
      (complex f M).liftCycles (i := 0) (augment f M) 1 (by simp) (augment_d f M) ≫
        (complex f M).homologyπ 0 := rfl

end FLT.Mazur.LocalizationCech

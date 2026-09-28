/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TildePrincipalOpen
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.RingTheory.LocalProperties.Exactness

/-!
# The principal-open localization Čech complex

The unnormalized Čech complex uses all tuples of indices. Its terms are actual
sections of the tilde module on principal opens, identified with localizations
by `termEquiv`. The differential is the alternating sum of restriction maps.
We construct the augmentation and prove its injectivity for a spanning family,
and give a local criterion for exactness. All-degree exactness still requires
a contraction after localizing at each member of the cover.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite PrimeSpectrum
open scoped Simplicial

universe u

namespace FLT.Mazur.LocalizationCech

open TildePrincipalOpen

variable {R : CommRingCat.{u}} {ι : Type u} (f : ι → R) (M : ModuleCat.{u} R)

/-- Degree `q` sections on all `(q+1)`-fold intersections. -/
abbrev term (q : ℕ) : ModuleCat R := (cechTermFunctor f q).obj M

/-- Each Čech term is the corresponding product of module localizations. -/
def termEquiv (q : ℕ) :
    term f M q ≃ₗ[R] (∀ s : Fin (q + 1) → ι, LocalizedModule (.powers (∏ j, f (s j))) M) :=
  familyEquiv _ M

/-- Reindexing a tuple can only enlarge its intersection open. -/
lemma intersection_le {p q : ℕ} (a : Fin (p + 1) → Fin (q + 1))
    (s : Fin (q + 1) → ι) :
    basicOpen (∏ j, f (s j)) ≤ basicOpen (∏ j, f (s (a j))) := by
  rw [cechTerm_open, cechTerm_open]
  exact le_iInf fun j ↦ iInf_le _ (a j)

/-- Reindexing sections and restricting to the smaller intersection. -/
def reindex {p q : ℕ} (a : Fin (p + 1) → Fin (q + 1)) : term f M p ⟶ term f M q :=
  ModuleCat.ofHom
    { toFun := fun x s ↦
        ((modulesSpecToSheaf.obj (tilde M)).presheaf.map
          (homOfLE (intersection_le f a s)).op).hom (x (s ∘ a))
      map_add' := fun x y ↦ funext fun s ↦ map_add _ _ _
      map_smul' := by
        intro r x
        funext s
        exact map_smul _ r (x (s ∘ a)) }

@[simp]
lemma reindex_id (q : ℕ) : reindex f M (id : Fin (q + 1) → _) = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext s
  change ((modulesSpecToSheaf.obj (tilde M)).presheaf.map (𝟙 _)).hom (x s) = x s
  simp

lemma reindex_comp {p q r : ℕ} (a : Fin (p + 1) → Fin (q + 1))
    (b : Fin (q + 1) → Fin (r + 1)) :
    reindex f M (b ∘ a) = reindex f M a ≫ reindex f M b := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext s
  change ((modulesSpecToSheaf.obj (tilde M)).presheaf.map _).hom _ =
    (((modulesSpecToSheaf.obj (tilde M)).presheaf.map _) ≫
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.map _)).hom _
  rw [← Functor.map_comp]
  rfl

/-- The cosimplicial module of sections on the intersections. -/
def cosimplicial : CosimplicialObject (ModuleCat R) where
  obj n := term f M n.len
  map a := reindex f M a.toOrderHom
  map_id _ := reindex_id f M _
  map_comp a b := reindex_comp f M a.toOrderHom b.toOrderHom

/-- The Čech cochain complex with the usual alternating differential. -/
def complex : CochainComplex (ModuleCat R) ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).obj (cosimplicial f M)

/-- The differential is the alternating sum of the maps omitting one index. -/
lemma differential (q : ℕ) :
    (complex f M).d q (q + 1) =
      ∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) • reindex f M i.succAbove := by
  simp only [complex, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d]
  rfl

/-- The augmentation into the degree-zero term. -/
abbrev augment : M ⟶ term f M 0 := (cechAugmentation f).app M

@[simp]
lemma reindex_augmentation {q : ℕ} (a : Fin 1 → Fin (q + 1)) (m : M)
    (s : Fin (q + 1) → ι) :
    (reindex f M a).hom ((augment f M).hom m) s =
      toSections M (∏ j, f (s j)) m := by
  exact congrArg (fun h ↦ h.hom m)
    (tilde.toOpen_res M _ _ (homOfLE (intersection_le f a s)))

/-- The augmentation followed by the first differential is zero. -/
lemma augment_d : augment f M ≫ (complex f M).d 0 1 = 0 := by
  rw [differential, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_one_zsmul]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  funext s
  change (reindex f M (0 : Fin 2).succAbove).hom ((augment f M).hom m) s -
    (reindex f M (1 : Fin 2).succAbove).hom ((augment f M).hom m) s = 0
  simp only [reindex_augmentation, sub_self]

/-- The augmented complex, with `M` in degree zero and Čech degree `q` in degree `q+1`. -/
def augmentedComplex : CochainComplex (ModuleCat R) ℕ :=
  (complex f M).augment (augment f M) (augment_d f M)

/-- Sections on a spanning principal family jointly detect equality. -/
lemma sections_jointly_injective (hf : Ideal.span (Set.range f) = ⊤) (x y : M)
    (h : ∀ i, toSections M (f i) x = toSections M (f i) y) : x = y := by
  apply Module.eq_of_isLocalized_span (Set.range f) hf
    (fun r ↦ sections M r.1) (fun r ↦ toSections M r.1) x y
  rintro ⟨r, i, rfl⟩
  exact h i

/-- Exactness at the coefficient term of the augmented complex. -/
lemma augment_injective (hf : Ideal.span (Set.range f) = ⊤) :
    Function.Injective (augment f M).hom := by
  intro x y h
  apply sections_jointly_injective f M hf x y
  intro i
  have hi := congrFun h (fun _ ↦ i)
  change toSections M (∏ _ : Fin 1, f i) x = toSections M (∏ _ : Fin 1, f i) y at hi
  rw [Fin.prod_univ_one] at hi
  exact hi

/-- The augmented complex is exact at its initial coefficient module. -/
lemma augmentedComplex_exactAt_zero (hf : Ideal.span (Set.range f) = ⊤) :
    (augmentedComplex f M).ExactAt 0 := by
  rw [(augmentedComplex f M).exactAt_iff' 0 0 1 (by simp) (by simp),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  change Function.Exact (0 : M →ₗ[R] M) (augment f M).hom
  exact (LinearMap.exact_zero_iff_injective M _).mpr (augment_injective f M hf)

/-- Exactness of coefficient maps is detected by a spanning family of principal opens. -/
lemma exact_iff_sections (hf : Ideal.span (Set.range f) = ⊤)
    {X Y Z : ModuleCat.{u} R} (a : X ⟶ Y) (b : Y ⟶ Z) :
    Function.Exact a.hom b.hom ↔ ∀ i,
      Function.Exact ((sectionsFunctor (f i)).map a).hom
        ((sectionsFunctor (f i)).map b).hom := by
  constructor
  · intro h i
    exact sections_exact (f i) a b h
  · intro h
    apply exact_of_isLocalized_span (Set.range f) hf
      (fun r ↦ sections X r.1) (fun r ↦ toSections X r.1)
      (fun r ↦ sections Y r.1) (fun r ↦ toSections Y r.1)
      (fun r ↦ sections Z r.1) (fun r ↦ toSections Z r.1) a.hom b.hom
    rintro ⟨r, i, rfl⟩
    simpa only [sectionsFunctor_map] using! h i

/-- Exactness at any position of a complex is local on a spanning principal family. -/
lemma exactAt_iff_sections (hf : Ideal.span (Set.range f) = ⊤)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) :
    K.ExactAt q ↔ ∀ i,
      (((sectionsFunctor (f i)).mapHomologicalComplex (.up ℕ)).obj K).ExactAt q := by
  simp only [HomologicalComplex.exactAt_iff,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact exact_iff_sections f hf _ _

end FLT.Mazur.LocalizationCech

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizationCech
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# Localization of the principal-open Čech terms

Localization at `r` identifies each finite Čech term with sections on the
intersections `D(r * ∏ j, f (s j))`. The comparison respects every reindexing
map, hence every coface, and the augmentation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite PrimeSpectrum

universe u

namespace FLT.Mazur.LocalizationCechCompare

open TildePrincipalOpen LocalizationCech

/-- Cancelling the first localization in localization away from a product. -/
lemma away_in_stages {R : Type*} [CommRing R]
    {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module R X] [Module R Y] [Module R Z] (r g : R)
    (b : X →ₗ[R] Y) (c : Y →ₗ[R] Z)
    [IsLocalizedModule.Away g b] [IsLocalizedModule.Away (r * g) (c.comp b)] :
    IsLocalizedModule.Away r c := by
  have hu := IsLocalizedModule.Away.isUnit_algebraMap (c.comp b) (r * g)
  rw [map_mul] at hu
  obtain ⟨hr, hg⟩ := ((Commute.all r g).map _).isUnit_mul_iff.mp hu
  have cancel (n : ℕ) : Function.Injective (fun z : Z ↦ g ^ n • z) := by
    have h : IsUnit (algebraMap R (Module.End R Z) (g ^ n)) := by
      rw [map_pow]
      exact hg.pow n
    exact (Module.End.isUnit_iff _).mp h |>.1
  refine IsLocalizedModule.Away.mk_of_addCommGroup hr ?_ ?_
  · intro z
    obtain ⟨n, x, hx⟩ := IsLocalizedModule.Away.surj (c.comp b) (r * g) z
    obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff _).mp
      (IsLocalizedModule.map_units b (⟨g ^ n, n, rfl⟩ : Submonoid.powers g))).2 (b x)
    refine ⟨n, y, cancel n ?_⟩
    change g ^ n • y = b x at hy
    simpa only [mul_pow, mul_smul, smul_comm (r ^ n) (g ^ n),
      LinearMap.comp_apply, ← map_smul, hy] using hx
  · intro y hy
    obtain ⟨k, x, hx⟩ := IsLocalizedModule.Away.surj b g y
    have hz : (c.comp b) x = 0 := by rw [LinearMap.comp_apply, ← hx, map_smul, hy, smul_zero]
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (.powers (r * g))
      (c.comp b)).mp hz
    refine ⟨n, IsLocalizedModule.smul_injective b
      (⟨g ^ (n + k), n + k, rfl⟩ : Submonoid.powers g) ?_⟩
    have hb := congrArg b hn
    simpa only [Submonoid.smul_def, map_smul, map_zero, mul_pow, mul_smul,
      ← hx, pow_add, smul_zero, smul_comm (r ^ n) (g ^ n),
      smul_comm (r ^ n) (g ^ k)] using hb

variable {R : CommRingCat.{u}} {ι : Type u} (f : ι → R) (M : ModuleCat.{u} R)

/-- Restriction from `D(g)` to `D(rg)`, with the fixed factor first. -/
def baseRestriction (r g : R) : sections M g →ₗ[R] sections M (r * g) :=
  ((modulesSpecToSheaf.obj (tilde M)).presheaf.map
    (homOfLE (basicOpen_mul_le_right r g)).op).hom

@[simp]
lemma baseRestriction_toSections (r g : R) (m : M) :
    baseRestriction M r g (toSections M g m) = toSections M (r * g) m := rfl

instance baseRestriction_isLocalized (r g : R) :
    IsLocalizedModule (.powers r) (baseRestriction M r g) := by
  have h : (baseRestriction M r g).comp (toSections M g) =
      toSections M (r * g) := by ext; rfl
  have : IsLocalizedModule.Away (r * g)
      ((baseRestriction M r g).comp (toSections M g)) := by rw [h]; infer_instance
  exact away_in_stages r g (toSections M g) (baseRestriction M r g)

/-- Localization in stages, expressed using actual principal-open sections. -/
def stagesEquiv (r g : R) : sections (sections M g) r ≃ₗ[R] sections M (r * g) :=
  IsLocalizedModule.linearEquiv (.powers r)
    (toSections (sections M g) r) (baseRestriction M r g)

@[simp]
lemma stagesEquiv_toSections (r g : R) (x : sections M g) :
    stagesEquiv M r g (toSections (sections M g) r x) = baseRestriction M r g x :=
  IsLocalizedModule.linearEquiv_apply _ _ _ _

/-- The term of the Čech complex restricted to `D(r)`. -/
abbrev baseTerm (r : R) (q : ℕ) : ModuleCat R :=
  ModuleCat.of R (∀ s : Fin (q + 1) → ι, sections M (r * ∏ j, f (s j)))

/-- Termwise restriction to intersections with `D(r)`. -/
def toBaseTerm (r : R) (q : ℕ) : term f M q →ₗ[R] baseTerm f M r q :=
  .pi fun s ↦ (baseRestriction M r (∏ j, f (s j))).comp (.proj s)

instance toBaseTerm_isLocalized [Finite ι] (r : R) (q : ℕ) :
    IsLocalizedModule (.powers r) (toBaseTerm f M r q) :=
  IsLocalizedModule.pi _ _

/-- The finite-product localization comparison for the section functor. -/
def compare [Finite ι] (r : R) (q : ℕ) :
    sections (term f M q) r ≃ₗ[R] baseTerm f M r q :=
  IsLocalizedModule.linearEquiv (.powers r)
    (toSections (term f M q) r) (toBaseTerm f M r q)

@[simp]
lemma compare_toSections [Finite ι] (r : R) (q : ℕ) (x : term f M q) :
    compare f M r q (toSections (term f M q) r x) = toBaseTerm f M r q x :=
  IsLocalizedModule.linearEquiv_apply _ _ _ _

/-- The same comparison with the explicit localized module as source. -/
def localizedCompare [Finite ι] (r : R) (q : ℕ) :
    LocalizedModule (.powers r) (term f M q) ≃ₗ[R] baseTerm f M r q :=
  IsLocalizedModule.iso (.powers r) (toBaseTerm f M r q)

@[simp]
lemma localizedCompare_mk [Finite ι] (r : R) (q : ℕ) (x : term f M q) :
    localizedCompare f M r q (LocalizedModule.mk x 1) = toBaseTerm f M r q x :=
  IsLocalizedModule.iso_mk_one _ _ _

/-- Reindexing intersection sections inside the fixed principal open. -/
def baseReindex (r : R) {p q : ℕ} (a : Fin (p + 1) → Fin (q + 1)) :
    baseTerm f M r p ⟶ baseTerm f M r q :=
  ModuleCat.ofHom
    { toFun := fun x s ↦
        ((modulesSpecToSheaf.obj (tilde M)).presheaf.map
          (homOfLE (show basicOpen (r * ∏ j, f (s j)) ≤
              basicOpen (r * ∏ j, f (s (a j))) by
            simpa only [basicOpen_mul] using inf_le_inf_left (basicOpen r)
              (intersection_le f a s))).op).hom (x (s ∘ a))
      map_add' := fun x y ↦ funext fun s ↦ map_add _ _ _
      map_smul' := fun t x ↦ funext fun s ↦ map_smul _ t (x (s ∘ a)) }

/-- Restriction to `D(r)` commutes with every tuple reindexing. -/
lemma toBaseTerm_reindex (r : R) {p q : ℕ} (a : Fin (p + 1) → Fin (q + 1)) :
    (toBaseTerm f M r q).comp (reindex f M a).hom =
      (baseReindex f M r a).hom.comp (toBaseTerm f M r p) := by
  ext x s
  change (((modulesSpecToSheaf.obj (tilde M)).presheaf.map _) ≫
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.map _)).hom _ =
    (((modulesSpecToSheaf.obj (tilde M)).presheaf.map _) ≫
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.map _)).hom _
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- The localized comparison commutes with all reindexings, including every coface. -/
lemma compare_reindex [Finite ι] (r : R) {p q : ℕ}
    (a : Fin (p + 1) → Fin (q + 1)) :
    (compare f M r q).toLinearMap.comp ((sectionsFunctor r).map (reindex f M a)).hom =
      (baseReindex f M r a).hom.comp (compare f M r p).toLinearMap := by
  apply IsLocalizedModule.linearMap_ext (.powers r)
    (toSections (term f M p) r) (toBaseTerm f M r q)
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, sectionsFunctor_map, IsLocalizedModule.map_apply,
    LinearEquiv.coe_coe]
  rw [compare_toSections, compare_toSections]
  exact DFunLike.congr_fun (toBaseTerm_reindex f M r a) x

/-- Explicit module localization has the same coface compatibility. -/
lemma localizedCompare_reindex [Finite ι] (r : R) {p q : ℕ}
    (a : Fin (p + 1) → Fin (q + 1)) :
    (localizedCompare f M r q).toLinearMap.comp
        (IsLocalizedModule.map (.powers r)
          (LocalizedModule.mkLinearMap (.powers r) (term f M p))
          (LocalizedModule.mkLinearMap (.powers r) (term f M q)) (reindex f M a).hom) =
      (baseReindex f M r a).hom.comp (localizedCompare f M r p).toLinearMap := by
  apply IsLocalizedModule.linearMap_ext (.powers r)
    (LocalizedModule.mkLinearMap (.powers r) (term f M p)) (toBaseTerm f M r q)
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LocalizedModule.mkLinearMap_apply, IsLocalizedModule.map_LocalizedModules]
  rw [localizedCompare_mk, localizedCompare_mk]
  exact DFunLike.congr_fun (toBaseTerm_reindex f M r a) x

/-- The augmentation on the cover restricted to `D(r)`. -/
def baseAugment (r : R) : sections M r ⟶ baseTerm f M r 0 :=
  ModuleCat.ofHom (R := R) (X := sections M r) (Y := baseTerm f M r 0)
    { toFun := fun x s ↦ restriction M r (∏ j, f (s j)) x
      map_add' := fun x y ↦ funext fun _s ↦ map_add _ x y
      map_smul' := fun t x ↦ funext fun _s ↦ map_smul _ t x }

/-- The comparison identifies the localized augmentation with actual restriction. -/
lemma compare_augment [Finite ι] (r : R) :
    (compare f M r 0).toLinearMap.comp ((sectionsFunctor r).map (augment f M)).hom =
      (baseAugment f M r).hom := by
  apply IsLocalizedModule.linearMap_ext (.powers r)
    (toSections M r) (toBaseTerm f M r 0)
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, sectionsFunctor_map, IsLocalizedModule.map_apply,
    LinearEquiv.coe_coe]
  rw [compare_toSections]
  rfl

/-- The comparison is natural in the coefficient module. -/
lemma compare_naturality [Finite ι] {N : ModuleCat.{u} R} (a : M ⟶ N)
    (r : R) (q : ℕ) :
    (compare f N r q).toLinearMap.comp
        ((sectionsFunctor r).map ((cechTermFunctor f q).map a)).hom =
      ((familyFunctor (fun s : Fin (q + 1) → ι ↦ r * ∏ j, f (s j))).map a).hom.comp
        (compare f M r q).toLinearMap := by
  apply IsLocalizedModule.linearMap_ext (.powers r)
    (toSections (term f M q) r) (toBaseTerm f N r q)
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, sectionsFunctor_map, IsLocalizedModule.map_apply,
    LinearEquiv.coe_coe]
  change compare f N r q (toSections (term f N q) r _) =
    ((familyFunctor (fun s : Fin (q + 1) → ι ↦ r * ∏ j, f (s j))).map a).hom
      (compare f M r q (toSections (term f M q) r x))
  rw [compare_toSections, compare_toSections]
  funext s
  exact congrArg (fun h ↦ h.hom (x s))
    (((modulesSpecToSheaf.map ((tilde.functor R).map a)).hom.naturality
      (homOfLE (basicOpen_mul_le_right r (∏ j, f (s j)))).op).symm)

@[simp]
lemma baseReindex_id (r : R) (q : ℕ) :
    baseReindex f M r (id : Fin (q + 1) → _) = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext s
  change ((modulesSpecToSheaf.obj (tilde M)).presheaf.map (𝟙 _)).hom (x s) = x s
  simp

lemma baseReindex_comp (r : R) {p q t : ℕ} (a : Fin (p + 1) → Fin (q + 1))
    (b : Fin (q + 1) → Fin (t + 1)) :
    baseReindex f M r (b ∘ a) = baseReindex f M r a ≫ baseReindex f M r b := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext s
  change ((modulesSpecToSheaf.obj (tilde M)).presheaf.map _).hom _ =
    (((modulesSpecToSheaf.obj (tilde M)).presheaf.map _) ≫
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.map _)).hom _
  rw [← Functor.map_comp]
  rfl

/-- The cosimplicial section module on intersections with a fixed principal open. -/
def baseCosimplicial (r : R) : CosimplicialObject (ModuleCat R) where
  obj n := baseTerm f M r n.len
  map a := baseReindex f M r a.toOrderHom
  map_id _ := baseReindex_id f M r _
  map_comp a b := baseReindex_comp f M r a.toOrderHom b.toOrderHom

/-- The section complex on the cover restricted to `D(r)`. -/
def baseComplex (r : R) : CochainComplex (ModuleCat R) ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).obj (baseCosimplicial f M r)

lemma baseDifferential (r : R) (q : ℕ) :
    (baseComplex f M r).d q (q + 1) =
      ∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) • baseReindex f M r i.succAbove := by
  simp only [baseComplex, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d]
  rfl

set_option maxHeartbeats 800000 in
-- Unifying the bundled section modules across the alternating sums is expensive.
/-- The term comparisons intertwine the alternating differentials. -/
lemma compare_differential [Finite ι] (r : R) (q : ℕ) :
    (sectionsFunctor r).map ((complex f M).d q (q + 1)) ≫
        (compare f M r (q + 1)).toModuleIso.hom =
      (compare f M r q).toModuleIso.hom ≫ (baseComplex f M r).d q (q + 1) := by
  rw [differential, baseDifferential]
  simp only [Functor.map_sum, Functor.map_zsmul, Preadditive.sum_comp,
    Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply ModuleCat.hom_ext
  exact compare_reindex f M r i.succAbove

/-- The restricted augmentation followed by the first differential is zero. -/
lemma baseAugment_d (r : R) :
    baseAugment f M r ≫ (baseComplex f M r).d 0 1 = 0 := by
  rw [baseDifferential, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_one_zsmul]
  have h (a : Fin 1 → Fin 2) (x : sections M r) (s : Fin 2 → ι) :
      (baseReindex f M r a).hom ((baseAugment f M r).hom x) s =
        restriction M r (∏ j, f (s j)) x := by
    change (((modulesSpecToSheaf.obj (tilde M)).presheaf.map _) ≫
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.map _)).hom x = _
    rw [← Functor.map_comp]
    rfl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext s
  change (baseReindex f M r (0 : Fin 2).succAbove).hom ((baseAugment f M r).hom x) s -
    (baseReindex f M r (1 : Fin 2).succAbove).hom ((baseAugment f M r).hom x) s = 0
  rw [h, h, sub_self]

/-- The restricted augmented complex, with sections on `D(r)` in degree zero. -/
def baseAugmentedComplex (r : R) : CochainComplex (ModuleCat R) ℕ :=
  (baseComplex f M r).augment (baseAugment f M r) (baseAugment_d f M r)

/-- A complex isomorphism ready for transporting a contraction on `D(r)`. -/
def complexIso [Finite ι] (r : R) :
    (((sectionsFunctor r).mapHomologicalComplex (.up ℕ)).obj (complex f M)) ≅
      baseComplex f M r :=
  HomologicalComplex.Hom.isoOfComponents (fun q ↦ (compare f M r q).toModuleIso)
    (by
      intro p q h
      obtain rfl : p + 1 = q := h
      exact (compare_differential f M r p).symm)

end FLT.Mazur.LocalizationCechCompare

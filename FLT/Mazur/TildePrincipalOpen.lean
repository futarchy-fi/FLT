/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Tilde modules on principal opens

Sections on `D(f)` are the localization at the powers of `f`. The comparison
respects coefficient maps, restriction to `D(fg)`, and the global-section comparison.
Exactness in the coefficient module also holds on products of principal opens,
as required degree by degree for an augmented Čech complex.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite PrimeSpectrum

universe u

namespace FLT.Mazur.TildePrincipalOpen

variable {R : CommRingCat.{u}}

/-- The actual sections of the tilde sheaf on a principal open, with base scalars. -/
abbrev sections (M : ModuleCat.{u} R) (f : R) : ModuleCat R :=
  (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (.op (basicOpen f))

/-- Taking sections on a principal open, as a functor of the coefficient module. -/
def sectionsFunctor (f : R) : ModuleCat R ⥤ ModuleCat R :=
  tilde.functor R ⋙ modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _ ⋙
    (evaluation _ _).obj (.op (basicOpen f))

/-- The canonical localization map into principal-open sections. -/
abbrev toSections (M : ModuleCat.{u} R) (f : R) : M →ₗ[R] sections M f :=
  (tilde.toOpen M (basicOpen f)).hom

/-- The unique extension of the section action from `R` to `R_f`. -/
instance sectionsModule (M : ModuleCat.{u} R) (f : R) :
    Module (Localization.Away f) (sections M f) :=
  IsLocalizedModule.module (.powers f) (toSections M f)

instance sectionsScalarTower (M : ModuleCat.{u} R) (f : R) :
    IsScalarTower R (Localization.Away f) (sections M f) :=
  IsLocalizedModule.isScalarTower_module (.powers f) (toSections M f)

/-- The principal-open comparison, linear over the localized ring. -/
def sectionsEquiv (M : ModuleCat.{u} R) (f : R) :
    sections M f ≃ₗ[Localization.Away f] LocalizedModule (.powers f) M :=
  { (IsLocalizedModule.iso (.powers f) (toSections M f)).symm with
    map_smul' := (IsLocalization.linearMap_compatibleSMul (.powers f)
      (Localization.Away f) _ _).map_smul _ }

@[simp]
lemma sectionsEquiv_toSections (M : ModuleCat.{u} R) (f : R) (m : M) :
    sectionsEquiv M f (toSections M f m) = LocalizedModule.mk m 1 :=
  IsLocalizedModule.iso_symm_apply _ _ _

/-- The map on sections is the universal localized coefficient map. -/
lemma sectionsFunctor_map (f : R) {M N : ModuleCat.{u} R} (a : M ⟶ N) :
    ((sectionsFunctor f).map a).hom =
      IsLocalizedModule.map (.powers f) (toSections M f) (toSections N f) a.hom := by
  apply IsLocalizedModule.linearMap_ext (.powers f) (toSections M f) (toSections N f)
  rw [IsLocalizedModule.map_comp]
  exact congrArg ModuleCat.Hom.hom (tilde.toOpen_map_app a (basicOpen f))

instance tildePrincipalOpenInst1 (f : R) : (sectionsFunctor f).Additive where
  map_add := by
    intros
    apply ModuleCat.hom_ext
    simp only [sectionsFunctor_map, ModuleCat.hom_add, map_add]

/-- Naturality of the comparison in the coefficient module. -/
lemma sectionsEquiv_naturality (f : R) {M N : ModuleCat.{u} R} (a : M ⟶ N)
    (x : sections M f) :
    sectionsEquiv N f ((sectionsFunctor f).map a x) =
      IsLocalizedModule.map (.powers f) (LocalizedModule.mkLinearMap (.powers f) M)
        (LocalizedModule.mkLinearMap (.powers f) N) a.hom (sectionsEquiv M f x) := by
  change sectionsEquiv N f (((sectionsFunctor f).map a).hom x) = _
  rw [sectionsFunctor_map]
  apply (IsLocalizedModule.iso (.powers f) (toSections N f)).injective
  simpa [sectionsEquiv] using!
    DFunLike.congr_fun (IsLocalizedModule.map_iso_commute (.powers f)
      (toSections M f) (toSections N f) a.hom) (sectionsEquiv M f x)

/-- Restriction of actual sheaf sections from `D(f)` to `D(fg)`. -/
def restriction (M : ModuleCat.{u} R) (f g : R) :
    sections M f →ₗ[R] sections M (f * g) :=
  ((modulesSpecToSheaf.obj (tilde M)).presheaf.map
    (homOfLE (basicOpen_mul_le_left f g)).op).hom

@[simp]
lemma restriction_toSections (M : ModuleCat.{u} R) (f g : R) (m : M) :
    restriction M f g (toSections M f m) = toSections M (f * g) m := rfl

lemma localizationUnits (M : ModuleCat.{u} R) (f g : R)
    (s : Submonoid.powers f) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule (.powers (f * g)) M)) s) := by
  obtain ⟨s, n, rfl⟩ := s
  rw [map_pow]
  apply IsUnit.pow
  have h := IsLocalizedModule.Away.isUnit_algebraMap (r := f * g)
    (LocalizedModule.mkLinearMap (.powers (f * g)) M)
  rw [map_mul] at h
  exact ((Commute.all f g).map _).isUnit_mul_iff.mp h |>.1

/-- The algebraic localization map `M_f → M_fg`, obtained from its universal property. -/
def localizationRestriction (M : ModuleCat.{u} R) (f g : R) :
    LocalizedModule (.powers f) M →ₗ[R] LocalizedModule (.powers (f * g)) M :=
  IsLocalizedModule.lift (.powers f) (LocalizedModule.mkLinearMap (.powers f) M)
    (LocalizedModule.mkLinearMap (.powers (f * g)) M) (localizationUnits M f g)

@[simp]
lemma localizationRestriction_mk (M : ModuleCat.{u} R) (f g : R) (m : M) :
    localizationRestriction M f g (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 :=
  IsLocalizedModule.lift_apply _ _ _ _ _

/-- The section/localization comparison commutes with restriction. -/
lemma sectionsEquiv_restriction (M : ModuleCat.{u} R) (f g : R) (x : sections M f) :
    sectionsEquiv M (f * g) (restriction M f g x) =
      localizationRestriction M f g (sectionsEquiv M f x) := by
  have h :
      ((sectionsEquiv M (f * g)).restrictScalars R).toLinearMap.comp
          (restriction M f g) =
        (localizationRestriction M f g).comp
          ((sectionsEquiv M f).restrictScalars R).toLinearMap := by
    apply IsLocalizedModule.ext (.powers f) (toSections M f) (localizationUnits M f g)
    ext m
    simp
  exact DFunLike.congr_fun h x

/-- Compatibility with Mathlib's global-section identification. -/
lemma sectionsEquiv_from_global (M : ModuleCat.{u} R) (f : R) (m : M) :
    sectionsEquiv M f
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.map (basicOpen f).leTop.op
        ((tilde.isoTop M).hom m)) = LocalizedModule.mk m 1 :=
  sectionsEquiv_toSections M f m

/-- Principal-open sections preserve exact pairs of coefficient maps. -/
lemma sections_exact (f : R) {M N P : ModuleCat.{u} R} (a : M ⟶ N) (b : N ⟶ P)
    (h : Function.Exact a.hom b.hom) :
    Function.Exact ((sectionsFunctor f).map a).hom ((sectionsFunctor f).map b).hom := by
  rw [sectionsFunctor_map, sectionsFunctor_map]
  exact IsLocalizedModule.map_exact (.powers f)
    (toSections M f) (toSections N f) (toSections P f) a.hom b.hom h

/-- Principal-open sections preserve injections. -/
lemma sections_injective (f : R) {M N : ModuleCat.{u} R} (a : M ⟶ N)
    (h : Function.Injective a.hom) : Function.Injective ((sectionsFunctor f).map a).hom := by
  rw [sectionsFunctor_map]
  exact IsLocalizedModule.map_injective (.powers f) (toSections M f) (toSections N f) a.hom h

/-- Principal-open sections preserve surjections. -/
lemma sections_surjective (f : R) {M N : ModuleCat.{u} R} (a : M ⟶ N)
    (h : Function.Surjective a.hom) : Function.Surjective ((sectionsFunctor f).map a).hom := by
  rw [sectionsFunctor_map]
  exact IsLocalizedModule.map_surjective (.powers f) (toSections M f) (toSections N f) a.hom h

/-- Taking sections of tilde modules on a principal open is exact. -/
lemma sectionsFunctor_exact (f : R) (S : ShortComplex (ModuleCat.{u} R)) (h : S.Exact) :
    (S.map (sectionsFunctor f)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact sections_exact f S.f S.g h

/-- A short exact coefficient sequence gives a short exact sequence on every `D(f)`. -/
lemma sectionsFunctor_shortExact (f : R) (S : ShortComplex (ModuleCat.{u} R))
    (h : S.ShortExact) : (S.map (sectionsFunctor f)).ShortExact where
  exact := sectionsFunctor_exact f S h.exact
  mono_f := (ModuleCat.mono_iff_injective _).mpr (sections_injective f S.f h.injective_f)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (sections_surjective f S.g h.surjective_g)

instance tildePrincipalOpenInst2 (f : R) : Limits.PreservesFiniteLimits (sectionsFunctor f) := by
  have h := ((Functor.exact_tfae (sectionsFunctor f)).out 2 4).mp (sectionsFunctor_exact f)
  exact h.1

instance tildePrincipalOpenInst3 (f : R) : Limits.PreservesFiniteColimits (sectionsFunctor f) := by
  have h := ((Functor.exact_tfae (sectionsFunctor f)).out 2 4).mp (sectionsFunctor_exact f)
  exact h.2

variable {ι : Type u}

/-- Products of principal-open sections, functorial in the coefficient module. -/
def familyFunctor (d : ι → R) : ModuleCat R ⥤ ModuleCat R where
  obj M := ModuleCat.of R (∀ i, sections M (d i))
  map a := ModuleCat.ofHom
    { toFun := fun x i ↦ ((sectionsFunctor (d i)).map a).hom (x i)
      map_add' := fun x y ↦ funext fun i ↦ map_add _ (x i) (y i)
      map_smul' := fun r x ↦ funext fun i ↦ map_smul _ r (x i) }
  map_id M := by ext x i; exact congrArg (fun a ↦ a.hom (x i)) ((sectionsFunctor _).map_id M)
  map_comp a b := by
    ext x i
    exact congrArg (fun a ↦ a.hom (x i)) ((sectionsFunctor _).map_comp a b)

instance tildePrincipalOpenInst4 (d : ι → R) : (familyFunctor d).Additive where
  map_add := by
    intro M N a b
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    exact congrArg (fun a ↦ a.hom (x i))
      ((sectionsFunctor (d i)).map_add (f := a) (g := b))

/-- The product comparison used to identify Čech terms with localization terms. -/
def familyEquiv (d : ι → R) (M : ModuleCat.{u} R) :
    (familyFunctor d).obj M ≃ₗ[R] (∀ i, LocalizedModule (.powers (d i)) M) :=
  LinearEquiv.piCongrRight fun i ↦ (sectionsEquiv M (d i)).restrictScalars R

/-- Restricting global coefficients to a family of principal opens, naturally in `M`. -/
def augmentation (d : ι → R) : 𝟭 (ModuleCat R) ⟶ familyFunctor d where
  app M := ModuleCat.ofHom (LinearMap.pi fun i ↦ toSections M (d i))
  naturality {M N} a := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    funext i
    exact (congrArg (fun a ↦ a.hom m) (tilde.toOpen_map_app a (basicOpen (d i)))).symm

lemma familyEquiv_augmentation (d : ι → R) (M : ModuleCat.{u} R) (m : M) (i : ι) :
    familyEquiv d M ((augmentation d).app M m) i = LocalizedModule.mk m 1 :=
  sectionsEquiv_toSections M (d i) m

/-- Exactness is preserved by the product of principal-open section functors. -/
lemma familyFunctor_exact (d : ι → R) (S : ShortComplex (ModuleCat.{u} R)) (h : S.Exact) :
    (S.map (familyFunctor d)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  intro y
  change (fun i ↦ ((sectionsFunctor (d i)).map S.g).hom (y i)) = 0 ↔
    ∃ x : ∀ i, sections S.X₁ (d i), (fun i ↦ ((sectionsFunctor (d i)).map S.f).hom (x i)) = y
  constructor
  · intro hy
    have hi (i) := (sections_exact (d i) S.f S.g h (y i)).mp (congrFun hy i)
    choose x hx using hi
    exact ⟨x, funext hx⟩
  · rintro ⟨x, rfl⟩
    exact funext fun i ↦ (sections_exact (d i) S.f S.g h).apply_apply_eq_zero (x i)

/-- Products of principal-open section sequences are short exact. -/
lemma familyFunctor_shortExact (d : ι → R) (S : ShortComplex (ModuleCat.{u} R))
    (h : S.ShortExact) : (S.map (familyFunctor d)).ShortExact where
  exact := familyFunctor_exact d S h.exact
  mono_f := (ModuleCat.mono_iff_injective _).mpr
    (Function.Injective.piMap fun i ↦ sections_injective (d i) S.f h.injective_f)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr
    (Function.Surjective.piMap fun i ↦ sections_surjective (d i) S.g h.surjective_g)

/-- A finite intersection of principal opens is the principal open of the product. -/
lemma basicOpen_prod {κ : Type*} (s : Finset κ) (d : κ → R) :
    basicOpen (∏ i ∈ s, d i) = ⨅ i ∈ s, basicOpen (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.prod_insert hi, basicOpen_mul, ih, Finset.iInf_insert]

/-- The coefficient functor for degree `n` of the Čech complex of principal opens. -/
abbrev cechTermFunctor (f : ι → R) (n : ℕ) : ModuleCat R ⥤ ModuleCat R :=
  familyFunctor (fun s : Fin (n + 1) → ι ↦ ∏ j, f (s j))

/-- The Čech augmentation from coefficients into the degree-zero section term. -/
abbrev cechAugmentation (f : ι → R) : 𝟭 (ModuleCat R) ⟶ cechTermFunctor f 0 :=
  augmentation (fun s : Fin 1 → ι ↦ ∏ j, f (s j))

/-- These are the actual intersection opens in the Čech term. -/
lemma cechTerm_open (f : ι → R) (n : ℕ) (s : Fin (n + 1) → ι) :
    basicOpen (∏ j, f (s j)) = ⨅ j, basicOpen (f (s j)) := by
  simpa using basicOpen_prod Finset.univ (fun j ↦ f (s j))

/-- Degreewise coefficient exactness for the Čech complex of a finite principal cover.
The assertion needs no covering hypothesis, so it applies in particular when the
`f i` generate the unit ideal. The augmented coefficient term is the original `S`. -/
lemma cechTerm_shortExact (f : ι → R)
    (S : ShortComplex (ModuleCat.{u} R)) (h : S.ShortExact) (n : ℕ) :
    (S.map (cechTermFunctor f n)).ShortExact :=
  familyFunctor_shortExact _ S h

end FLT.Mazur.TildePrincipalOpen

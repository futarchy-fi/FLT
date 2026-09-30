/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentGenericExtension
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.Colon

/-!
# Affine ideal-power extension of coherent morphisms

Containment after localization along generators of an ideal gives containment
of an ideal-power multiple. Artin–Rees then removes the kernel of a map that
is invertible on the complementary principal opens. This is the coefficient
step for extending a morphism from an open subscheme. The actual affine extension
is obtained from the two projections of its extended graph, with agreement on
the whole open complement of the given finitely generated ideal.
-/

@[expose] public noncomputable section

open Submodule

universe u v w

namespace FLT.Mazur.IdealPowerLifting

open AffineCoherentSubmoduleExtension

variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]

/-- Finitely many numerators have a common principal denominator. -/
lemma finite_denominator (s : Finset M) (Q : Submodule R M) (r : R)
    (h : ∀ x ∈ s, ∃ n : ℕ, r ^ n • x ∈ Q) :
    ∃ n : ℕ, ∀ x ∈ s, r ^ n • x ∈ Q := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x s hx ih =>
    obtain ⟨a, ha⟩ := h x (Finset.mem_insert_self _ _)
    obtain ⟨b, hb⟩ := ih (fun y hy ↦ h y (Finset.mem_insert_of_mem hy))
    refine ⟨a + b, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · simpa only [pow_add, mul_smul, smul_comm (r ^ a) (r ^ b)] using Q.smul_mem (r ^ b) ha
    · simpa only [pow_add, mul_smul] using Q.smul_mem (r ^ a) (hb y hy)

/-- A localized containment of a finite submodule clears one power for the whole submodule. -/
lemma principal_denominator (P Q : Submodule R M) (hP : P.FG) (r : R)
    (h : P.localized (.powers r) ≤ Q.localized (.powers r)) :
    ∃ n : ℕ, ∀ x ∈ P, r ^ n • x ∈ Q := by
  obtain ⟨s, hs⟩ := hP
  obtain ⟨n, hn⟩ := finite_denominator s Q r (fun x hx ↦
    (numerator_mem_away_iff Q r x).mp (h ((numerator_mem_away_iff P r x).mpr
      ⟨0, by simpa using (hs ▸ Submodule.subset_span hx : x ∈ P)⟩)))
  refine ⟨n, ?_⟩
  intro x hx
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hn x hx
  | zero => simp
  | add x y _ _ hx hy => simpa only [smul_add] using Q.add_mem hx hy
  | smul a x _ hx => simpa only [smul_comm (r ^ n) a] using Q.smul_mem a hx

/-- Local containment on the complement of a finitely generated ideal clears an ideal power. -/
theorem exists_pow_smul_le_of_localized_le (P Q : Submodule R M) (hP : P.FG)
    (s : Finset R) (h : ∀ r ∈ s, P.localized (.powers r) ≤ Q.localized (.powers r)) :
    ∃ n : ℕ, (Ideal.span (s : Set R)) ^ n • P ≤ Q := by
  have hr : Ideal.span (s : Set R) ≤ (Q.colon (P : Set M)).radical := by
    apply Ideal.span_le.mpr
    intro r hr
    obtain ⟨n, hn⟩ := principal_denominator P Q hP r (h r hr)
    exact ⟨n, Submodule.mem_colon.mpr hn⟩
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hr (Submodule.fg_span s.finite_toSet)
  exact ⟨n, Submodule.smul_le.mpr fun r hr x hx ↦ Submodule.mem_colon.mp (hn hr) x hx⟩

/-- Artin–Rees makes a sufficiently deep ideal multiple disjoint from supported torsion. -/
theorem exists_pow_inf_eq_bot [IsNoetherianRing R] [Module.Finite R M]
    (s : Finset R) (K : Submodule R M)
    (h : ∀ r ∈ s, K.localized (.powers r) = ⊥) :
    ∃ n : ℕ, (Ideal.span (s : Set R)) ^ n • (⊤ : Submodule R M) ⊓ K = ⊥ := by
  let J := Ideal.span (s : Set R)
  obtain ⟨a, ha⟩ := exists_pow_smul_le_of_localized_le K ⊥
    (IsNoetherian.noetherian K) s (fun r hr ↦ by simp [h r hr, Submodule.localized])
  obtain ⟨b, hb⟩ := J.exists_pow_inf_eq_pow_smul K
  refine ⟨a + b, le_bot_iff.mp ?_⟩
  rw [hb (a + b) (Nat.le_add_left b a), Nat.add_sub_cancel_right]
  exact (smul_le_smul_left (J ^ a) inf_le_right).trans ha

/-- The kernel disappears on every principal open where the localized map is injective. -/
lemma localized_ker_eq_bot (f : M →ₗ[R] N) (r : R)
    (h : Function.Injective (LocalizedModule.map (.powers r) f)) :
    f.ker.localized (.powers r) = ⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨m, hm, a, rfl⟩
  apply h
  change IsLocalizedModule.map (.powers r) _ _ f _ = _
  simp only [IsLocalizedModule.map_mk', LinearMap.mem_ker.mp hm,
    IsLocalizedModule.mk'_zero, map_zero]

/-- Surjectivity on a principal localization makes the localized range the whole module. -/
lemma localized_range_eq_top (f : M →ₗ[R] N) (r : R)
    (h : Function.Surjective (LocalizedModule.map (.powers r) f)) :
    f.range.localized (.powers r) = ⊤ := by
  rw [Submodule.localized, LinearMap.localized'_range_eq_range_localizedMap
    (Localization.Away r) (.powers r) (LocalizedModule.mkLinearMap (.powers r) M)
    (LocalizedModule.mkLinearMap (.powers r) N)]
  exact LinearMap.range_eq_top.mpr h

/-- A map invertible off the ideal has an injective deep multiple with large image. -/
theorem exists_injective_pow_image [IsNoetherianRing R]
    [Module.Finite R M] [Module.Finite R N] (f : M →ₗ[R] N) (s : Finset R)
    (h : ∀ r ∈ s, Function.Bijective (LocalizedModule.map (.powers r) f)) :
    ∃ a b : ℕ,
      Function.Injective (f.domRestrict ((Ideal.span (s : Set R)) ^ a • ⊤)) ∧
      (Ideal.span (s : Set R)) ^ b • (⊤ : Submodule R N) ≤
        ((Ideal.span (s : Set R)) ^ a • (⊤ : Submodule R M)).map f := by
  let J := Ideal.span (s : Set R)
  obtain ⟨a, ha⟩ := exists_pow_inf_eq_bot s f.ker
    (fun r hr ↦ localized_ker_eq_bot f r (h r hr).injective)
  obtain ⟨c, hc⟩ := exists_pow_smul_le_of_localized_le ⊤ f.range Module.Finite.fg_top s
    (fun r hr ↦ by rw [localized_range_eq_top f r (h r hr).surjective]; exact le_top)
  refine ⟨a, a + c, ?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hm : x.val - y.val ∈ (J ^ a • ⊤ : Submodule R M) ⊓ f.ker :=
      ⟨sub_mem x.property y.property, by
        change f (x.val - y.val) = 0
        exact (map_sub f _ _).trans (sub_eq_zero.mpr hxy)⟩
    rw [ha] at hm
    exact hm
  · rw [pow_add, mul_smul, Submodule.map_smul'', Submodule.map_top]
    exact smul_le_smul_left (J ^ a) hc

/-- Invert a map on a submodule where it is injective and whose image contains the source. -/
def liftFromImage (f : M →ₗ[R] N) (P : Submodule R M) (Q : Submodule R N)
    (hi : Function.Injective (f.domRestrict P)) (hq : Q ≤ P.map f) : Q →ₗ[R] M :=
  P.subtype ∘ₗ (LinearEquiv.ofInjective (f.domRestrict P) hi).symm.toLinearMap ∘ₗ
    Q.subtype.codRestrict (f.domRestrict P).range (fun x ↦ by
      simpa only [LinearMap.domRestrict, LinearMap.range_comp, Submodule.range_subtype,
        Submodule.subtype_apply] using hq x.property)

/-- The constructed lift maps back to the original element. -/
lemma liftFromImage_commutes (f : M →ₗ[R] N) (P : Submodule R M) (Q : Submodule R N)
    (hi : Function.Injective (f.domRestrict P)) (hq : Q ≤ P.map f) (x : Q) :
    f (liftFromImage f P Q hi hq x) = x := by
  exact congrArg Subtype.val ((LinearEquiv.ofInjective (f.domRestrict P) hi).apply_symm_apply
    (Q.subtype.codRestrict (f.domRestrict P).range (fun y ↦ by
      simpa only [LinearMap.domRestrict, LinearMap.range_comp, Submodule.range_subtype,
        Submodule.subtype_apply] using hq y.property) x))

/-- A finite map invertible off an ideal has a constructed lift from an ideal-power multiple. -/
theorem exists_idealPower_lift [IsNoetherianRing R]
    [Module.Finite R M] [Module.Finite R N] (f : M →ₗ[R] N) (s : Finset R)
    (h : ∀ r ∈ s, Function.Bijective (LocalizedModule.map (.powers r) f)) :
    ∃ n : ℕ, ∃ g : ↥((Ideal.span (s : Set R)) ^ n • (⊤ : Submodule R N)) →ₗ[R] M,
      ∀ x, f (g x) = x := by
  obtain ⟨a, b, hi, hq⟩ := exists_injective_pow_image f s h
  exact ⟨b, liftFromImage f _ _ hi hq, liftFromImage_commutes f _ _ hi hq⟩

end FLT.Mazur.IdealPowerLifting

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite PrimeSpectrum
open Scheme.Modules


namespace FLT.Mazur.AffineIdealPowerExtension

open PrincipalSubmoduleCoordinates AffineCoherentSubmoduleRestriction
open FCurve FCurve.CoherentDevissage CoherentGenericExtension IdealPowerLifting

variable {R : CommRingCat.{u}} {M N : (Spec R).Modules}

/-- A sheaf isomorphism on an open is bijective on every smaller open's sections. -/
lemma app_bijective_of_restrict (f : M ⟶ N) (U V : (Spec R).Opens) (hV : V ≤ U)
    [IsIso ((restrictFunctor U.ι).map f)] : Function.Bijective (f.app V) := by
  let W := U.ι ⁻¹ᵁ V
  let E := SheafOfModules.evaluation U.toScheme.ringCatSheaf (op W)
  have h := ConcreteCategory.bijective_of_isIso (E.map ((restrictFunctor U.ι).map f))
  change Function.Bijective (f.app (U.ι ''ᵁ W)) at h
  have he : U.ι ''ᵁ W = V := by
    dsimp only [W]
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hV]
  rwa [he] at h

/-- Actual principal section maps are the localizations of the coefficient maps. -/
lemma principal_map (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] (r : R) :
    ((modulesSpecToSheaf.map f).hom.app (op (basicOpen r))).hom =
      IsLocalizedModule.map (.powers r) (toSections M r) (toSections N r)
        (moduleSpecΓFunctor.map f).hom := by
  apply IsLocalizedModule.linearMap_ext (.powers r) (toSections M r) (toSections N r)
  rw [IsLocalizedModule.map_comp]
  ext x
  exact congr($((modulesSpecToSheaf.map f).hom.naturality (basicOpen r).leTop.op) x)

/-- Invertibility on a containing open gives invertibility of the localized coefficients. -/
lemma coefficient_bijective (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (U : (Spec R).Opens) [IsIso ((restrictFunctor U.ι).map f)] (r : R)
    (hr : basicOpen r ≤ U) :
    Function.Bijective (LocalizedModule.map (.powers r) (moduleSpecΓFunctor.map f).hom) := by
  let eM := IsLocalizedModule.iso (.powers r) (toSections M r)
  let eN := IsLocalizedModule.iso (.powers r) (toSections N r)
  have h := IsLocalizedModule.map_iso_commute (.powers r) (toSections M r) (toSections N r)
    (moduleSpecΓFunctor.map f).hom
  rw [← principal_map f r] at h
  have he : (LocalizedModule.map (.powers r) (moduleSpecΓFunctor.map f).hom :
      LocalizedModule (.powers r) (moduleSpecΓFunctor.obj M) →
      LocalizedModule (.powers r) (moduleSpecΓFunctor.obj N)) =
      eN.symm ∘ f.app (basicOpen r) ∘ eM := by
    funext x
    apply eN.injective
    change eN _ = eN (eN.symm _)
    rw [LinearEquiv.apply_symm_apply]
    exact (DFunLike.congr_fun h x).symm
  rw [he]
  exact eN.symm.bijective.comp
    ((app_bijective_of_restrict f U (basicOpen r) hr).comp eM.bijective)

/-- The actual affine ideal-power multiple, formed from the source's global sections. -/
def powerMultiple (M : (Spec R).Modules) (J : Ideal R) (n : ℕ) : (Spec R).Modules :=
  tilde (ModuleCat.of R ↥(J ^ n • (⊤ : Submodule R (moduleSpecΓFunctor.obj M))))

/-- Its canonical inclusion into the original source. -/
def powerMultipleι (M : (Spec R).Modules) (J : Ideal R) (n : ℕ) :
    powerMultiple M J n ⟶ M := coefficientInclusion M (J ^ n • ⊤)

instance powerMultiple_coherent [IsNoetherianRing R] [M.IsFinitePresentation]
    (J : Ideal R) (n : ℕ) : (powerMultiple M J n).IsFinitePresentation := by
  have : Module.Finite R (moduleSpecΓFunctor.obj M) := affineCoherent_finite_sections M
  exact affineTilde_isFinitePresentation_of_finite _

instance powerMultipleι_mono [M.IsQuasicoherent] (J : Ideal R) (n : ℕ) :
    Mono (powerMultipleι M J n) := coefficientInclusion_mono _ _

/-- A finite principal cover determines the open complementary to its generated ideal. -/
def complement (s : Finset R) : (Spec R).Opens := ⨆ r : s, basicOpen (r : R)

/-- Affine coherent morphisms extend from a constructed ideal-power multiple.
The equation is the comparison square on the entire original open. -/
theorem exists_extension [IsNoetherianRing R]
    [M.IsFinitePresentation] [N.IsFinitePresentation] (s : Finset R)
    (g : M.restrict (complement s).ι ⟶ N.restrict (complement s).ι) :
    ∃ n : ℕ, ∃ f : powerMultiple M (Ideal.span (s : Set R)) n ⟶ N,
      (restrictFunctor (complement s).ι).map f =
        (restrictFunctor (complement s).ι).map (powerMultipleι M _ n) ≫ g := by
  let U := complement s
  let T := restrictFunctor U.ι
  obtain ⟨P, hP, b, _, e, _, hp, hq⟩ := exists_graph_extension U.ι M N g
  let p := b ≫ biprod.fst
  let q := b ≫ biprod.snd
  have : IsIso (T.map p) := by change IsIso ((restrictFunctor U.ι).map _); rw [hp]; infer_instance
  have : Module.Finite R (moduleSpecΓFunctor.obj P) := affineCoherent_finite_sections P
  have : Module.Finite R (moduleSpecΓFunctor.obj M) := affineCoherent_finite_sections M
  obtain ⟨n, l, hl⟩ := exists_idealPower_lift (moduleSpecΓFunctor.map p).hom s
    (fun r hr ↦ coefficient_bijective p U r (le_iSup (fun r : s ↦ basicOpen (r : R)) ⟨r, hr⟩))
  let a : powerMultiple M (Ideal.span (s : Set R)) n ⟶ P :=
    (tilde.functor R).map (ModuleCat.ofHom l) ≫ P.fromTildeΓ
  have ha : a ≫ p = powerMultipleι M (Ideal.span (s : Set R)) n := by
    have hn : (tilde.functor R).map (moduleSpecΓFunctor.map p) ≫ M.fromTildeΓ =
        P.fromTildeΓ ≫ p := fromTildeΓNatTrans.naturality p
    change ((tilde.functor R).map (ModuleCat.ofHom l) ≫ P.fromTildeΓ) ≫ p = _
    dsimp only [powerMultipleι, coefficientInclusion]
    rw [Category.assoc, ← hn, ← Category.assoc,
      ← Functor.map_comp]
    congr 2
    apply ModuleCat.hom_ext
    ext x
    exact hl x
  refine ⟨n, a ≫ q, ?_⟩
  rw [Functor.map_comp, show T.map q = e.hom ≫ g from hq,
    ← hp, ← Category.assoc, ← Functor.map_comp, ha]

/-- The complement is exactly the complement of the vanishing locus of the generated ideal. -/
lemma complement_coe (s : Finset R) :
    (complement s : Set (Spec R)) = (zeroLocus (Ideal.span (s : Set R) : Set R))ᶜ := by
  ext x
  change (x ∈ ⨆ r : s, (basicOpen (r : R) : (Spec R).Opens)) ↔ _
  rw [Opens.mem_iSup]
  change (∃ r : s, (r : R) ∉ x.asIdeal) ↔ x ∉ zeroLocus (Ideal.span (s : Set R) : Set R)
  rw [zeroLocus_span, mem_zeroLocus]
  simp only [Set.not_subset, Subtype.exists, exists_prop, SetLike.mem_coe]

/-- The open complement of the given ideal. -/
def idealComplement (J : Ideal R) : (Spec R).Opens :=
  ⟨(zeroLocus (J : Set R))ᶜ, (isClosed_zeroLocus _).isOpen_compl⟩

/-- The extension theorem for a given finitely generated ideal, without chosen generators. -/
theorem exists_extension_of_fg [IsNoetherianRing R]
    [M.IsFinitePresentation] [N.IsFinitePresentation] (J : Ideal R) (hJ : J.FG)
    (g : M.restrict (idealComplement J).ι ⟶ N.restrict (idealComplement J).ι) :
    ∃ n : ℕ, ∃ f : powerMultiple M J n ⟶ N,
      (restrictFunctor (idealComplement J).ι).map f =
        (restrictFunctor (idealComplement J).ι).map (powerMultipleι M J n) ≫ g := by
  obtain ⟨s, rfl⟩ := hJ
  have he : idealComplement (Ideal.span (s : Set R)) = complement s :=
    Opens.ext (complement_coe s).symm
  generalize hu : idealComplement (Ideal.span (s : Set R)) = U at g ⊢
  rw [he] at hu
  subst U
  exact exists_extension s g

end FLT.Mazur.AffineIdealPowerExtension

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCohomologyVanishingLocal
public import FLT.Mazur.LocalizationCechExact
public import FLT.Mazur.LocalizationCechIso

/-!
# Finite principal covers for local cohomology vanishing

Principal opens refine every cover of a compact open in an affine spectrum.
Consequently every positive Ext class vanishes on a finite principal cover.
For the whole spectrum the resulting elements generate the unit ideal, which
is the hypothesis of localization Cech exactness. Local vanishing alone does
not imply global vanishing; the cofinal-cover descent step remains separate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace FLT.Mazur.AffineCohomologyVanishingCovers

open AffineCohomologyVanishingLocal

variable {R : CommRingCat.{u}}

/-- A property stable under shrinking and valid locally holds on a finite principal cover. -/
lemma exists_finite_principal_cover (W : Opens (PrimeSpectrum R))
    (hW : IsCompact (W : Set (PrimeSpectrum R))) (P : Opens (PrimeSpectrum R) → Prop)
    (hP : ∀ V V', V ≤ V' → P V' → P V)
    (hloc : ∀ x ∈ W, ∃ V : Opens (PrimeSpectrum R), x ∈ V ∧ V ≤ W ∧ P V) :
    ∃ s : Finset R, (⨆ f : s, PrimeSpectrum.basicOpen (f : R)) = W ∧
      ∀ f ∈ s, P (PrimeSpectrum.basicOpen f) := by
  classical
  have hbasic : ∀ x : W, ∃ f : R,
      x.val ∈ PrimeSpectrum.basicOpen f ∧ PrimeSpectrum.basicOpen f ≤ W ∧
        P (PrimeSpectrum.basicOpen f) := by
    intro x
    obtain ⟨V, hxV, hVW, hPV⟩ := hloc x.val x.property
    obtain ⟨_, ⟨f, rfl⟩, hxf, hfV⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxV V.isOpen
    exact ⟨f, hxf, le_trans hfV hVW, hP _ _ hfV hPV⟩
  choose f hxf hfW hfP using hbasic
  obtain ⟨t, ht⟩ := hW.elim_finite_subcover
    (fun x : W ↦ (PrimeSpectrum.basicOpen (f x) : Set (PrimeSpectrum R)))
    (fun _ ↦ (PrimeSpectrum.basicOpen _).isOpen) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxf ⟨x, hx⟩⟩)
  refine ⟨t.image f, le_antisymm ?_ ?_, ?_⟩
  · refine iSup_le fun a ↦ ?_
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp a.property
    exact hx ▸ hfW x
  · intro x hx
    obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Opens.mem_iSup.mpr ⟨⟨f y, Finset.mem_image.mpr ⟨y, hyt, rfl⟩⟩, hxy⟩
  · intro a ha
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
    exact hfP x

/-- Finite principal covers are cofinal among open covers of a compact open. -/
lemma exists_finite_principal_refinement (W : Opens (PrimeSpectrum R))
    (hW : IsCompact (W : Set (PrimeSpectrum R))) {ι : Type*}
    (U : ι → Opens (PrimeSpectrum R)) (hU : W ≤ iSup U) :
    ∃ s : Finset R, (⨆ f : s, PrimeSpectrum.basicOpen (f : R)) = W ∧
      ∀ f ∈ s, ∃ i, PrimeSpectrum.basicOpen f ≤ U i := by
  apply exists_finite_principal_cover W hW (fun V ↦ ∃ i, V ≤ U i)
  · rintro V V' hVV' ⟨i, hi⟩
    exact ⟨i, le_trans hVV' hi⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU hx)
    exact ⟨W ⊓ U i, ⟨hx, hi⟩, inf_le_left, i, inf_le_right⟩

/-- A5's exactness also holds in the actual sheaf Cech complex. -/
lemma principal_cech_exactAt {ι : Type u} [Finite ι] (f : ι → R)
    (M : ModuleCat.{u} R) (hf : Ideal.span (Set.range f) = ⊤) (n : ℕ) :
    ((cechComplexFunctor (fun i ↦ PrimeSpectrum.basicOpen (f i))).obj
      (FCurve.moduleAbelianSheaf (tilde M)).obj).ExactAt (n + 1) := by
  have h := LocalizationCechExact.exactAt_succ f M hf n
  change ((LocalizationCech.complex f M).sc (n + 1)).Exact at h
  have hmap : (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (LocalizationCech.complex f M)).ExactAt (n + 1) :=
    h.map (forget₂ (ModuleCat R) AddCommGrpCat)
  exact hmap.of_iso (localizationCechIso f M)

/-- Positive sheaf Cech cohomology is zero on every finite spanning principal cover. -/
lemma principal_cech_isZero {ι : Type u} [Finite ι] (f : ι → R)
    (M : ModuleCat.{u} R) (hf : Ideal.span (Set.range f) = ⊤) (n : ℕ) :
    IsZero (((cechComplexFunctor (fun i ↦ PrimeSpectrum.basicOpen (f i))).obj
      (FCurve.moduleAbelianSheaf (tilde M)).obj).homology (n + 1)) :=
  (principal_cech_exactAt f M hf n).isZero_homology

variable [HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology (TopCat.of (Spec R))) AddCommGrpCat.{u})]

/-- A positive class on a compact open vanishes on a finite principal cover of that open. -/
lemma exists_finite_principal_zero
    (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Spec R))) (n : ℕ)
    (W : Opens (PrimeSpectrum R)) (hW : IsCompact (W : Set (PrimeSpectrum R)))
    (a : F.H' (n + 1) W) :
    ∃ s : Finset R, (⨆ f : s, PrimeSpectrum.basicOpen (f : R)) = W ∧
      ∀ f ∈ s, ∃ i : PrimeSpectrum.basicOpen f ⟶ W,
        (F.cohomologyPresheaf (n + 1)).map i.op a = 0 := by
  apply exists_finite_principal_cover W hW
    (fun V ↦ ∃ i : V ⟶ W, (F.cohomologyPresheaf (n + 1)).map i.op a = 0)
  · intro V V' hVV' h
    obtain ⟨i, hi⟩ := h
    refine ⟨homOfLE hVV' ≫ i, ?_⟩
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hi, map_zero]
  · intro x hx
    obtain ⟨V, i, hxV, hi⟩ := exists_neighborhood_zero n F W a x hx
    exact ⟨V, hxV, leOfHom i, i, hi⟩

/-- In particular, local vanishing on a basic open has a finite principal witness. -/
lemma exists_basicOpen_cover_zero
    (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Spec R))) (n : ℕ) (r : R)
    (a : F.H' (n + 1) (PrimeSpectrum.basicOpen r)) :
    ∃ s : Finset R, (⨆ f : s, PrimeSpectrum.basicOpen (f : R)) =
        PrimeSpectrum.basicOpen r ∧
      ∀ f ∈ s, ∃ i : PrimeSpectrum.basicOpen f ⟶ PrimeSpectrum.basicOpen r,
        (F.cohomologyPresheaf (n + 1)).map i.op a = 0 :=
  exists_finite_principal_zero F n _ (PrimeSpectrum.isCompact_basicOpen r) a

/-- Global positive Ext classes vanish on some finite unit-ideal principal cover. -/
lemma exists_spanning_principal_zero
    (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (Spec R))) (n : ℕ)
    (a : Sheaf.H F (n + 1)) :
    ∃ s : Finset R, Ideal.span (Set.range fun f : s ↦ (f : R)) = ⊤ ∧
      ∀ f ∈ s, restrictSheafH F (n + 1) (PrimeSpectrum.basicOpen f) a = 0 := by
  obtain ⟨s, hs, hzero⟩ := exists_finite_principal_zero F n ⊤
    (by simpa using (isCompact_univ : IsCompact (Set.univ : Set (PrimeSpectrum R))))
    (restrictSheafH F (n + 1) ⊤ a)
  refine ⟨s, PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp hs, ?_⟩
  intro f hf
  obtain ⟨i, hi⟩ := hzero f hf
  exact (restrictSheafH_naturality F (n + 1) i a).symm.trans hi

end FLT.Mazur.AffineCohomologyVanishingCovers

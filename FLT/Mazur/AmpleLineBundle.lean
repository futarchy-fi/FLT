/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleHomIsomorphismOpen
public import FLT.Mazur.RelativeVeryAmpleLineBundle

/-!
# Ample invertible sheaves via affine section opens

This is the section definition of Stacks 01PR: the scheme is quasi-compact,
the sheaf is invertible, and affine nonvanishing opens of positive-power
sections cover it. The relative definition follows Stacks 01VG. No projective
presentation or descent conclusion is included in either predicate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
variable {X : Scheme.{u}} {L M N : X.Modules}

/-- Postcomposition by an isomorphism preserves the actual invertibility open. -/
lemma moduleHomIsoOpen_comp_iso (f : L ⟶ M) (e : M ≅ N) :
    moduleHomIsoOpen (f ≫ e.hom) = moduleHomIsoOpen f := by
  apply le_antisymm
  · apply (le_moduleHomIsoOpen_iff _ _).mpr
    have h : IsIso ((restrictFunctor (moduleHomIsoOpen (f ≫ e.hom)).ι).map
        (f ≫ e.hom)) := inferInstance
    rw [Functor.map_comp] at h
    exact IsIso.of_isIso_comp_right _
      ((restrictFunctor (moduleHomIsoOpen (f ≫ e.hom)).ι).map e.hom)
  · apply (le_moduleHomIsoOpen_iff _ _).mpr
    rw [Functor.map_comp]
    infer_instance

/-- Isomorphisms carry sections to sections with exactly the same generator open. -/
lemma sectionGeneratorOpen_iso (e : L ≅ M) (s : Γ(L, ⊤)) :
    sectionGeneratorOpen M (e.hom.app ⊤ s) = sectionGeneratorOpen L s := by
  dsimp only [sectionGeneratorOpen]
  rw [← globalSectionHom_naturality, moduleHomIsoOpen_comp_iso]

/-- An ample invertible sheaf in the affine-section-open sense of Stacks 01PR. -/
def AmpleLineBundle (L : X.Modules) : Prop :=
  CompactSpace X ∧ LocallyFreeRankOne L ∧ ∀ x : X,
    ∃ (n : ℕ) (_ : 0 < n) (s : Γ(tensorPower L n, ⊤)),
      x ∈ sectionGeneratorOpen (tensorPower L n) s ∧
        IsAffineOpen (sectionGeneratorOpen (tensorPower L n) s)

/-- The standard ample predicate is invariant under isomorphism of sheaves. -/
theorem AmpleLineBundle.of_iso (h : AmpleLineBundle L) (e : M ≅ L) :
    AmpleLineBundle M := by
  refine ⟨h.1, h.2.1.of_iso e.symm, fun x ↦ ?_⟩
  obtain ⟨n, hn, s, hx, hs⟩ := h.2.2 x
  let en := tensorPowerCongr e.symm n
  refine ⟨n, hn, en.hom.app ⊤ s, ?_, ?_⟩
  · simpa only [sectionGeneratorOpen_iso] using hx
  · simpa only [sectionGeneratorOpen_iso] using hs

/-- Standard ampleness supplies a finite affine cover by actual positive-power
section opens; no global projective embedding is assumed. -/
theorem AmpleLineBundle.finite_section_cover (h : AmpleLineBundle L) :
    ∃ (ι : Type u) (_ : Finite ι) (n : ι → ℕ)
      (s : ∀ i, Γ(tensorPower L (n i), ⊤)),
      (∀ i, 0 < n i) ∧
      (∀ i, IsAffineOpen (sectionGeneratorOpen (tensorPower L (n i)) (s i))) ∧
      (⨆ i, sectionGeneratorOpen (tensorPower L (n i)) (s i)) = ⊤ := by
  classical
  let := h.1
  choose n hn s hx hs using h.2.2
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ (sectionGeneratorOpen (tensorPower L (n x)) (s x) : Set X))
    (fun x ↦ (sectionGeneratorOpen _ _).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  refine ⟨t, inferInstance, fun i ↦ n i, fun i ↦ s i,
    fun i ↦ hn i, fun i ↦ hs i, ?_⟩
  apply top_unique
  intro x _
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxi⟩

/-- The structure line bundle on every affine scheme is ample, including
schemes over nonreduced rings. -/
theorem ampleLineBundle_structure_of_affine [IsAffine X] :
    AmpleLineBundle (structureModule X) := by
  let e : tensorPower (structureModule X) 1 ≅ structureModule X :=
    ModuleSheafTensor.leftUnitor (structureModule X)
  let s : Γ(tensorPower (structureModule X) 1, ⊤) := e.inv.app ⊤ (1 : Γ(X, ⊤))
  have he : e.hom.app ⊤ s = (1 : Γ(X, ⊤)) :=
    ConcreteCategory.congr_hom (congrArg (fun f ↦ f.app ⊤) e.inv_hom_id) _
  have : IsIso (globalSectionHom _ s) :=
    globalSectionHom_isIso_of_coordinate _ s e (by rw [he]; exact isUnit_one)
  have hopen : sectionGeneratorOpen _ s = ⊤ :=
    top_unique (le_moduleHomIsoOpen _ ⊤)
  refine ⟨inferInstance, structureModule_locallyFreeRankOne, fun x ↦ ?_⟩
  exact ⟨1, by decide, s, hopen ▸ trivial, hopen ▸ isAffineOpen_top X⟩

/-- Relative ampleness of an invertible sheaf, as in Stacks 01VG. -/
def RelativelyAmpleLineBundle {S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) : Prop :=
  QuasiCompact f ∧ LocallyFreeRankOne L ∧
    ∀ (U : S.Opens), IsAffineOpen U → AmpleLineBundle (L.restrict (f ⁻¹ᵁ U).ι)

/-- Relative section ampleness is invariant under sheaf isomorphism. -/
theorem RelativelyAmpleLineBundle.of_iso {S : Scheme.{u}} {f : X ⟶ S}
    (h : RelativelyAmpleLineBundle f L) (e : M ≅ L) : RelativelyAmpleLineBundle f M := by
  refine ⟨h.1, h.2.1.of_iso e.symm, fun U hU ↦ ?_⟩
  exact (h.2.2 U hU).of_iso ((restrictFunctor (f ⁻¹ᵁ U).ι).mapIso e)

end FLT.Mazur.FCurve

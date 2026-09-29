/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveSectionExtension
public import FLT.Mazur.ProjectiveTwistTensorAddition

/-!
# Common-degree extensions of projective generators

Coordinate multiplication raises the degree of an extension without changing
its coefficient on the distinguished chart. Finite families of chart sections
therefore extend simultaneously in one twist.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Compatible chart coefficients glue to a global section of the indicated twist. -/
theorem compatibleCoordinates_global (F : (space R ι).Modules) (d : ℕ)
    (t : ∀ j, Γ(F, chart R ι j))
    (ht : ∀ j k, overlapDiscrepancy R ι F d t j k = 0) :
    ∃ σ : Γ(twistTensor R ι F (d : ℤ), ⊤), ∀ i,
      (twistAmbientIso R ι F (d : ℤ) i (chart R ι i) le_rfl).hom
        ((twistTensor R ι F (d : ℤ)).presheaf.map (homOfLE le_top).op σ) = t i := by
  let G := twistTensor R ι F (d : ℤ)
  let v := fun j ↦ (twistAmbientIso R ι F (d : ℤ) j _ le_rfl).inv (t j)
  have hv (j k : ι) : G.presheaf.map (homOfLE inf_le_left).op (v j) =
      G.presheaf.map (homOfLE inf_le_right).op (v k) := by
    dsimp only [v, G]
    rw [twistAmbientIso_inv_restrict, twistAmbientIso_inv_restrict]
    apply twistAmbientIso_inv_eq
    rw [twistTransition_restrict_self_pow]
    exact sub_eq_zero.mp (ht j k)
  obtain ⟨σ, hσ, _⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨G.presheaf, G.isSheaf⟩ : TopCat.Sheaf Ab (space R ι))
    (chart R ι) ⊤ (fun _ ↦ homOfLE le_top) (by rw [iSup_chart]) v hv
  refine ⟨σ, fun i ↦ ?_⟩
  change (twistAmbientIso R ι F (d : ℤ) i _ le_rfl).hom
    (G.presheaf.map (homOfLE le_top).op σ) = t i
  rw [hσ i]
  exact ConcreteCategory.congr_hom
    (twistAmbientIso R ι F (d : ℤ) i _ le_rfl).inv_hom_id (t i)

/-- Raising a compatible family preserves compatibility and its distinguished coefficient. -/
theorem compatibleCoordinates_raise (F : (space R ι).Modules) (n d : ℕ) (hnd : n ≤ d)
    (i : ι) (t : ∀ j, Γ(F, chart R ι j))
    (ht : ∀ j k, overlapDiscrepancy R ι F n t j k = 0) :
    correctedChartNumerators R ι F i (d - n) t i = t i ∧
      ∀ j k, overlapDiscrepancy R ι F d
        (correctedChartNumerators R ι F i (d - n) t) j k = 0 := by
  constructor
  · simp only [correctedChartNumerators, chartCoordinateSection_self, one_pow, one_smul]
  · intro j k
    conv_lhs => arg 4; rw [← Nat.add_sub_of_le hnd]
    rw [overlapDiscrepancy_corrected, ht, smul_zero]

/-- A chart section extends in every sufficiently large natural twist. -/
theorem sectionExtension_eventually [Finite ι] (F : (space R ι).Modules)
    [F.IsFinitePresentation] (i : ι) (s : Γ(F, chart R ι i)) :
    ∃ n : ℕ, ∀ d ≥ n, ∃ σ : Γ(twistTensor R ι F (d : ℤ), ⊤),
      (twistAmbientIso R ι F (d : ℤ) i (chart R ι i) le_rfl).hom
        ((twistTensor R ι F (d : ℤ)).presheaf.map (homOfLE le_top).op σ) = s := by
  obtain ⟨n, t, hi, ht⟩ := sectionExtension_compatibleCoordinates R ι F i s
  refine ⟨n, fun d hd ↦ ?_⟩
  obtain ⟨hfix, hcompat⟩ := compatibleCoordinates_raise R ι F n d hd i t ht
  obtain ⟨σ, hσ⟩ := compatibleCoordinates_global R ι F d _ hcompat
  exact ⟨σ, (hσ i).trans (hfix.trans hi)⟩

/-- Every finite family of chart sections has extensions of one common degree. -/
theorem finite_sections_common_twist [Finite ι] (F : (space R ι).Modules)
    [F.IsFinitePresentation] {κ : Type u} [Finite κ] (i : κ → ι)
    (s : ∀ a, Γ(F, chart R ι (i a))) :
    ∃ (d : ℕ) (σ : κ → Γ(twistTensor R ι F (d : ℤ), ⊤)), ∀ a,
      (twistAmbientIso R ι F (d : ℤ) (i a) (chart R ι (i a)) le_rfl).hom
        ((twistTensor R ι F (d : ℤ)).presheaf.map (homOfLE le_top).op (σ a)) = s a := by
  classical
  let finiteIndex : Fintype κ := Fintype.ofFinite κ
  choose n hn using fun a ↦ sectionExtension_eventually R ι F (i a) (s a)
  let d := Finset.univ.sup n
  have hd (a : κ) : n a ≤ d := Finset.le_sup (Finset.mem_univ a)
  choose σ hσ using fun a ↦ hn a d (hd a)
  exact ⟨d, σ, hσ⟩

/-- Ambient inverse twist coordinates are linear over the functions on the open. -/
lemma twistAmbientIso_inv_smul (F : (space R ι).Modules) (d : ℤ) (i : ι)
    (V : (space R ι).Opens) (hi : V ≤ chart R ι i)
    (r : Γ(space R ι, V)) (s : Γ(F, V)) :
    (twistAmbientIso R ι F d i V hi).inv (r • s) =
      r • (twistAmbientIso R ι F d i V hi).inv s := by
  simp only [twistAmbientIso_inv, FCurve.ModuleSheafTensor.pure]
  change ((FCurve.ModuleSheafTensor.unit F (twistingSheaf R ι d)).app (op V)).hom
    ((r • s) ⊗ₜ[Γ(space R ι, V)] (twistCocycle R ι d).extend i hi 1) = _
  rw [← TensorProduct.smul_tmul', map_smul]

/-- The chart section comparison respects the transported coordinate-ring action. -/
lemma chartSectionsIso_smul (F : (space R ι).Modules) (i : ι)
    (r : chartRing R ι i) (s : chartSections R ι F i) :
    (chartSectionsIso R ι F i).hom (r • s) =
      ((space R ι).presheaf.map (eqToHom (chartMap_image_top R ι i).symm).op
        (((chartMap R ι i).appIso ⊤).inv
          ((Scheme.ΓSpecIso (.of (chartRing R ι i))).inv r))) •
      (chartSectionsIso R ι F i).hom s := by
  exact F.val.map_smul (eqToHom (chartMap_image_top R ι i).symm).op _ s

/-- Morphisms from a quasi-coherent affine sheaf are detected on actual global sections. -/
lemma affine_hom_ext_sections {A : CommRingCat.{u}} {M N : (Spec A).Modules}
    [M.IsQuasicoherent] (f g : M ⟶ N)
    (h : moduleSpecΓFunctor.map f = moduleSpecΓFunctor.map g) : f = g := by
  rw [← cancel_epi M.fromTildeΓ]
  have hf := Scheme.Modules.fromTildeΓNatTrans.naturality f
  have hg := Scheme.Modules.fromTildeΓNatTrans.naturality g
  exact hf.symm.trans ((congrArg (fun a ↦ (tilde.functor A).map a ≫ N.fromTildeΓ) h).trans hg)

/-- Morphisms on projective space are detected by their restrictions to standard charts. -/
lemma hom_ext_chart_restrict {F G : (space R ι).Modules} (f g : F ⟶ G)
    (h : ∀ i, (Scheme.Modules.restrictFunctor (chartMap R ι i)).map f =
      (Scheme.Modules.restrictFunctor (chartMap R ι i)).map g) : f = g := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  apply TopCat.Presheaf.IsSheaf.section_ext G.isSheaf
  intro x hx
  have hx' : x ∈ ⨆ i, chart R ι i := by rw [iSup_chart]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
  let V := U ⊓ chart R ι i
  have hv : V ≤ chart R ι i := inf_le_right
  have he : chartMap R ι i ''ᵁ (chartMap R ι i ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    rw [← Scheme.Hom.image_top_eq_opensRange, chartMap_image_top]
    exact inf_eq_right.mpr hv
  have heq : f.app V = g.app V := by
    have e := congrArg (fun a ↦ a.app (chartMap R ι i ⁻¹ᵁ V)) (h i)
    change f.app (chartMap R ι i ''ᵁ (chartMap R ι i ⁻¹ᵁ V)) =
      g.app (chartMap R ι i ''ᵁ (chartMap R ι i ⁻¹ᵁ V)) at e
    rwa [he] at e
  refine ⟨V, inf_le_left, ⟨hx, hi⟩, ?_⟩
  change G.val.map (homOfLE (show V ≤ U from inf_le_left)).op (f.val.app (op U) s) =
    G.val.map (homOfLE (show V ≤ U from inf_le_left)).op (g.val.app (op U) s)
  rw [← PresheafOfModules.naturality_apply f.val,
    ← PresheafOfModules.naturality_apply g.val]
  exact ConcreteCategory.congr_hom heq _

/-- Chart section transport is natural in a sheaf morphism. -/
lemma chartSectionsIso_naturality {F G : (space R ι).Modules} (f : F ⟶ G) (i : ι)
    (s : chartSections R ι F i) :
    (chartSectionsIso R ι G i).hom
      (((Scheme.Modules.restrictFunctor (chartMap R ι i)).map f).app ⊤ s) =
      f.app (chart R ι i) ((chartSectionsIso R ι F i).hom s) := by
  exact (PresheafOfModules.naturality_apply f.val
    (eqToHom (chartMap_image_top R ι i).symm).op s).symm

/-- A global section gives a compatible section on the entire open site. -/
def globalSectionFamily {X : Scheme.{u}} (F : X.Modules) (s : Γ(F, ⊤)) : F.sections :=
  F.val.sectionsMk (fun U ↦ F.presheaf.map (homOfLE le_top).op s) (fun {_ _} f ↦ by
    change F.presheaf.map f (F.presheaf.map _ s) = F.presheaf.map _ s
    rw [← Functor.map_comp_apply]
    rfl)

/-- Evaluation at a family of actual global sections. -/
def globalEvaluation {X : Scheme.{u}} (F : X.Modules) {κ : Type u}
    (s : κ → Γ(F, ⊤)) : SheafOfModules.free κ ⟶ F :=
  F.freeHomEquiv.symm (fun a ↦ globalSectionFamily F (s a))

/-- Cancellation after evaluation implies equality on each restricted generator. -/
lemma globalEvaluation_cancel {X : Scheme.{u}} {F G : X.Modules} {κ : Type u}
    (s : κ → Γ(F, ⊤)) (f g : F ⟶ G)
    (h : globalEvaluation F s ≫ f = globalEvaluation F s ≫ g) (a : κ) (U : X.Opens) :
    f.app U (F.presheaf.map (homOfLE le_top).op (s a)) =
      g.app U (F.presheaf.map (homOfLE le_top).op (s a)) := by
  have he := congrArg (fun p ↦ G.freeHomEquiv p a) h
  rw [SheafOfModules.freeHomEquiv_comp_apply,
    SheafOfModules.freeHomEquiv_comp_apply] at he
  simp only [globalEvaluation, Equiv.apply_symm_apply] at he
  exact congrArg (fun t ↦ t.val (op U)) he

/-- The common-degree extensions of spanning chart families give an epimorphism. -/
theorem globalEvaluation_epi_of_chart_generators [Finite ι]
    (F : (space R ι).Modules) [F.IsFinitePresentation]
    (n : ι → ℕ) (s : ∀ i, Fin (n i) → chartSections R ι F i) (d : ℕ)
    (σ : (Σ i, Fin (n i)) → Γ(twistTensor R ι F (d : ℤ), ⊤))
    (hs : ∀ i, Submodule.span (chartRing R ι i) (Set.range (s i)) = ⊤)
    (hσ : ∀ i a, (twistAmbientIso R ι F (d : ℤ) i (chart R ι i) le_rfl).hom
      ((twistTensor R ι F (d : ℤ)).presheaf.map (homOfLE le_top).op (σ ⟨i, a⟩)) =
        (chartSectionsIso R ι F i).hom (s i a)) :
    Epi (globalEvaluation (twistTensor R ι F (d : ℤ)) σ) where
  left_cancellation {H} f g h := by
    let G := twistTensor R ι F (d : ℤ)
    apply hom_ext_chart_restrict R ι f g
    intro i
    have chartFinitePresentation : (chartModule R ι G i).IsFinitePresentation :=
      chartModule_isFinitePresentation R ι G i
    apply affine_hom_ext_sections
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    apply (ConcreteCategory.bijective_of_isIso (chartSectionsIso R ι _ i).hom).injective
    change (chartSectionsIso R ι H i).hom
      (((Scheme.Modules.restrictFunctor (chartMap R ι i)).map f).app ⊤ t) =
      (chartSectionsIso R ι H i).hom
        (((Scheme.Modules.restrictFunctor (chartMap R ι i)).map g).app ⊤ t)
    rw [chartSectionsIso_naturality, chartSectionsIso_naturality]
    let e := twistAmbientIso R ι F (d : ℤ) i (chart R ι i) le_rfl
    have hgen (a : Fin (n i)) :
        Scheme.Modules.Hom.app f (chart R ι i) (e.inv ((chartSectionsIso R ι F i).hom (s i a))) =
        Scheme.Modules.Hom.app g (chart R ι i) (e.inv ((chartSectionsIso R ι F i).hom (s i a))) := by
      rw [← hσ i a]
      have he (v : Γ(G, chart R ι i)) : e.inv (e.hom v) = v :=
        ConcreteCategory.congr_hom e.hom_inv_id v
      rw [he]
      exact globalEvaluation_cancel σ f g h ⟨i, a⟩ _
    have hall (m : chartSections R ι F i) :
        Scheme.Modules.Hom.app f (chart R ι i) (e.inv ((chartSectionsIso R ι F i).hom m)) =
        Scheme.Modules.Hom.app g (chart R ι i) (e.inv ((chartSectionsIso R ι F i).hom m)) := by
      have hm : m ∈ Submodule.span (chartRing R ι i) (Set.range (s i)) := by
        rw [hs i]; trivial
      induction hm using Submodule.span_induction with
      | mem m hm => obtain ⟨a, rfl⟩ := hm; exact hgen a
      | zero => simp only [map_zero]
      | add x y hx hy hxy hyx => simp only [map_add, hxy, hyx]
      | smul r x hx hfx =>
        rw [chartSectionsIso_smul]
        dsimp only [e]
        rw [twistAmbientIso_inv_smul, Scheme.Modules.Hom.app_smul,
          Scheme.Modules.Hom.app_smul, hfx]
    obtain ⟨m, hm⟩ :=
      (ConcreteCategory.bijective_of_isIso (chartSectionsIso R ι F i).hom).surjective
        (e.hom ((chartSectionsIso R ι G i).hom t))
    have he := hall m
    rw [hm] at he
    simpa only [← ConcreteCategory.comp_apply, Iso.hom_inv_id,
      ConcreteCategory.id_apply] using he

/-- Every locally finitely presented sheaf on finite-coordinate projective space
has a natural twist admitting a finite free epimorphism. -/
theorem exists_twist_finite_free_epi [Finite ι] (F : (space R ι).Modules)
    [F.IsFinitePresentation] :
    ∃ (d : ℕ) (κ : Type u) (_ : Finite κ)
      (p : SheafOfModules.free κ ⟶ twistTensor R ι F (d : ℤ)), Epi p := by
  obtain ⟨n, s, _, hs⟩ := finite_chart_generators R ι F
  let t : ∀ a : Σ i, Fin (n i), Γ(F, chart R ι a.1) :=
    fun a ↦ (chartSectionsIso R ι F a.1).hom (s a.1 a.2)
  obtain ⟨d, σ, hσ⟩ := finite_sections_common_twist R ι F
    (κ := Σ i, Fin (n i)) Sigma.fst t
  refine ⟨d, Σ i, Fin (n i), inferInstance, globalEvaluation _ σ, ?_⟩
  apply globalEvaluation_epi_of_chart_generators R ι F n s d σ hs
  intro i a
  exact hσ ⟨i, a⟩

end FLT.Mazur.ProjectiveSpace

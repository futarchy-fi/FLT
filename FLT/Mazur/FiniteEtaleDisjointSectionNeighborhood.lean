/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteEtaleSectionEqualityNeighborhood
public import FLT.Mazur.FiniteEtaleSectionCoverNeighborhood

/-!
# Disjoint section covers on a constructed affine neighborhood

A complete finite section cover becomes disjoint after removing repetitions
and shrinking around any specified base point. Both the whole inverse image
and the original section maps are retained on the neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteEtaleDisjointSectionNeighborhood
open FiniteEtaleSectionCoverNeighborhood
universe u
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (p : X ⟶ Y) [Etale p] [IsSeparated p]
  {n : ℕ} (s : Fin n → (Y ⟶ X)) (hs : ∀ i, s i ≫ p = 𝟙 Y)
  (hc : ∀ x : X, ∃ i, s i (p x) = x) (y : Y)

include hs hc in
/-- Remove repeated sheets and construct an affine neighborhood with a disjoint complete cover. -/
theorem exists_disjoint_cover :
    ∃ (W : Y.Opens) (m : ℕ) (r : Fin m → (W.toScheme ⟶ (p ⁻¹ᵁ W).toScheme)),
      IsAffineOpen W ∧ y ∈ W ∧
      (∀ i, r i ≫ (p ∣_ W) = 𝟙 _) ∧ (∀ i, IsOpenImmersion (r i)) ∧
      (∀ x : (p ⁻¹ᵁ W).toScheme, ∃ i, r i ((p ∣_ W) x) = x) ∧
      Pairwise (fun i j ↦ Disjoint (Set.range (r i)) (Set.range (r j))) := by
  classical
  obtain ⟨W, hW, hyW, hpattern⟩ :=
    FiniteEtaleSectionEqualityNeighborhood.exists_affine_constant_pattern p s hs y
  let I := Set.range (fun i ↦ s i y)
  let _ : Fintype I := Fintype.ofFinite I
  let a (i : I) : Fin n := i.property.choose
  have ha (i : I) : s (a i) y = i.val := i.property.choose_spec
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let r (i : Fin (Fintype.card I)) := restrictedSection p (s (a (e i))) (hs _) W
  have hr (i : Fin (Fintype.card I)) : r i ≫ (p ∣_ W) = 𝟙 W.toScheme :=
    restrictedSection_section p _ _ W
  refine ⟨W, Fintype.card I, r, hW, hyW, hr,
    fun i ↦ UnramifiedSectionImmersion.isOpenImmersion _ _ (hr i), ?_, ?_⟩
  · intro x
    obtain ⟨j, hj⟩ := hc x.val
    let k : I := ⟨s j y, ⟨j, rfl⟩⟩
    refine ⟨e.symm k, ?_⟩
    apply (p ⁻¹ᵁ W).ι.isOpenEmbedding.injective
    change (r (e.symm k) ≫ (p ⁻¹ᵁ W).ι) ((p ∣_ W) x) = x.val
    rw [restrictedSection_ι]
    change s (a (e (e.symm k))) (((p ∣_ W) ≫ W.ι) x) = x.val
    rw [Equiv.apply_symm_apply, morphismRestrict_ι]
    exact ((hpattern (a k) j (p x.val) x.property).mpr (ha k)).trans hj
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨v, hv⟩ ⟨w, hw⟩
    have hvw : v = w := by
      have h := congrArg (fun z ↦ (p ∣_ W) z) (hv.trans hw.symm)
      change (r i ≫ (p ∣_ W)) v = (r j ≫ (p ∣_ W)) w at h
      rw [hr, hr] at h
      exact h
    subst w
    have he : s (a (e i)) v.val = s (a (e j)) v.val := by
      have h := congrArg (fun z ↦ (p ⁻¹ᵁ W).ι z) (hv.trans hw.symm)
      change (r i ≫ (p ⁻¹ᵁ W).ι) v = (r j ≫ (p ⁻¹ᵁ W).ι) v at h
      simpa only [r, restrictedSection_ι, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
        using h
    have he' := (hpattern _ _ v.val v.property).mp he
    rw [ha, ha] at he'
    exact hij (e.injective (Subtype.ext he'))

end FLT.Mazur.FiniteEtaleDisjointSectionNeighborhood

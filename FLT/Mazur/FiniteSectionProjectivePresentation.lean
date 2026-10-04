/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionChartGenerators

/-!
# A projective presentation from finitely many chart generators

A dummy zero coordinate handles empty covers uniformly. Denominators and the
extended chart generators form a finite family, reindexed by Fin for the
existing projective morphism. Properness closes the resulting immersion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {L : X.Modules} {R : Type} [CommRing R]

/-- Specified affine chart generators give a closed projective presentation over a proper base. -/
theorem finiteSection_presentation (f : X ⟶ Spec (.of R)) [IsProper f]
    {ι : Type} [Finite ι] (U : ι → X.Opens) (hU : ∀ j, IsAffineOpen (U j))
    (hcover : ⨆ j, U j = ⊤) (d : ι → Γ(L, ⊤))
    (hd : ∀ j, sectionGeneratorOpen L (d j) = U j)
    (G : ∀ j, Finset Γ(X, U j)) (a : (Σ j, ↥(G j)) → Γ(L, ⊤))
    (hG : ∀ j, Subring.closure
      (Set.range (sectionChartScalars (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (U j)) ∪ (G j : Set Γ(X, U j))) = ⊤)
    (ha : ∀ j (b : G j), sectionRatioOn L (d j) (U j) (hd j).symm.le (a ⟨j, b⟩) = b.val) :
    Nonempty (VeryAmplePresentation f L) := by
  classical
  let := Fintype.ofFinite ι
  let κ := ι ⊕ (Σ j, ↥(G j))
  let n := Fintype.card κ
  let e : Option κ ≃ Fin (n + 1) := Fintype.equivOfCardEq (by simp [n])
  let v : Option κ → Γ(L, ⊤)
    | none => 0
    | some (.inl j) => d j
    | some (.inr b) => a b
  let t : Fin (n + 1) → Γ(L, ⊤) := fun k ↦ v (e.symm k)
  let idx (j : ι) := e (some (.inl j))
  have ht (j : ι) : t (idx j) = d j := by simp [t, idx, v]
  have hnum (b : Σ j, ↥(G j)) : t (e (some (.inr b))) = a b := by simp [t, v]
  have htop : ⨆ k, sectionGeneratorOpen L (t k) = ⊤ := by
    apply top_unique
    rw [← hcover]
    apply iSup_le
    intro j
    rw [← hd j, ← ht j]
    exact le_iSup (fun k ↦ sectionGeneratorOpen L (t k)) (idx j)
  let r := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let g := sectionProjectiveMorphism L n t htop r
  have hidx (j : ι) : sectionGeneratorOpen L (t (idx j)) = U j := by rw [ht, hd]
  have hsurj (j : ι) : Function.Surjective
      (sectionProjectiveChartRingMap L n t (idx j) (U j) (hidx j).symm.le
        (sectionChartScalars r (U j))) := by
    apply sectionProjectiveChartRingMap_surjective L n t (idx j) (U j) _ _ (G j) (hG j)
    intro b hb
    refine ⟨e (some (.inr ⟨j, ⟨b, hb⟩⟩)), ?_⟩
    simpa only [ht, hnum] using ha j ⟨b, hb⟩
  have : IsImmersion g := by
    let : MorphismProperty.RespectsRight (@IsImmersion) (@IsOpenImmersion) :=
      ⟨fun i hi f hf ↦ by
        let := hi
        let := hf
        exact IsImmersion.comp f i⟩
    apply IsZariskiLocalAtTarget.of_forall_source_exists_preimage (P := @IsImmersion)
    intro x
    obtain ⟨j, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show x ∈ ⨆ j, U j by rw [hcover]; trivial)
    refine ⟨chart R (Fin (n + 1)) (idx j), ?_, ?_⟩
    · have he : g ⁻¹ᵁ chart R (Fin (n + 1)) (idx j) = U j :=
        (sectionProjectiveMorphism_preimage_chart L n t htop r (idx j)).trans (hidx j)
      exact (show x ∈ g ⁻¹ᵁ chart R (Fin (n + 1)) (idx j) from he.symm ▸ hx)
    · rw [show g ⁻¹ᵁ chart R (Fin (n + 1)) (idx j) = U j from
        (sectionProjectiveMorphism_preimage_chart L n t htop r (idx j)).trans (hidx j)]
      rw [sectionProjectiveMorphism_onOpen L n t htop r (idx j) (U j) (hidx j).symm.le]
      exact sectionProjectiveChartMorphism_isImmersion L n t (idx j) (U j) _ (hU j) _ (hsurj j)
  exact ⟨sectionVeryAmplePresentation L n t htop f⟩

end FLT.Mazur.FCurve

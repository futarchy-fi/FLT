/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalAffineSchemeDetectingOpen
public import FLT.Mazur.OriginalGeometricallyIntegralOpen

/-!
# Uniform detecting neighborhoods on original geometric fibers

An original affine chart transports a nonempty detecting open into the
entire algebraic fiber. No point is chosen, so smooth lifting can select a
separable point while preserving all unchanged larger-field open conditions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OriginalSchemeDetectingOpen
set_option backward.isDefEq.respectTransparency false
variable {k L K : Type} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra L K] [Algebra k K] [IsScalarTower k L K]
  [Algebra.IsAlgebraic k L] {X Y Z : Scheme}

/-- A constructed nonempty open controls every rational point selected inside it. -/
theorem exists_detecting_open (f : X ⟶ Spec (.of k)) [GeometricallyIntegral f]
    (a : Y ⟶ Spec (.of K)) (b : Y ⟶ X)
    (H : IsPullback a b (Spec.map (CommRingCat.ofHom (algebraMap k K))) f)
    (c : Z ⟶ Spec (.of L)) (d : Z ⟶ X)
    (G : IsPullback c d (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)
    {J : Type*} [Finite J] (U : J → Y.Opens)
    (hU : ∀ j, (U j : Set Y).Nonempty) :
    ∃ (D : Scheme) (j : D ⟶ Z), IsOpenImmersion j ∧ Nonempty D ∧
      ∀ p : Spec (.of L) ⟶ D, p ≫ j ≫ c = 𝟙 _ →
        ∃ z : (L ≃ₐ[k] L) → (Spec (.of K) ⟶ Y),
          (∀ σ, z σ ≫ a = 𝟙 _) ∧
          (∀ σ, z σ ≫ b = Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫
            Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ p ≫ j ≫ d) ∧
          ∀ σ i, Set.range (z σ) ⊆ U i := by
  let _ : IsIntegral Y := GeometricallyIntegral.geometrically_isIntegral _ _ _ H.flip
  obtain ⟨y⟩ := IsIntegral.nonempty (X := Y)
  let n := X.affineCover.idx (b y)
  let A := X.affineCover.X n
  let i := X.affineCover.f n
  obtain ⟨w, hw⟩ := X.affineCover.covers (b y)
  let _ : Nonempty A := ⟨w⟩
  let _ : GeometricallyIntegral (i ≫ f) :=
    OriginalGeometricallyIntegralOpen.geometricallyIntegral i f
  let pK := pullback.snd i b
  let rK := pullback.fst i b
  let pL := pullback.snd i d
  let rL := pullback.fst i d
  have HK := (IsPullback.of_hasPullback i b).flip.paste_horiz H
  have HL := (IsPullback.of_hasPullback i d).flip.paste_horiz G
  obtain ⟨v, _, _⟩ := Scheme.Pullback.exists_preimage_pullback w y hw
  have hp : (Set.range pK).Nonempty := ⟨pK v, v, rfl⟩
  let U' (j : J) := pK ⁻¹ᵁ U j
  have hU' (j : J) : (U' j : Set (pullback i b : Scheme)).Nonempty := by
    obtain ⟨x, hx, v, hv⟩ := nonempty_preirreducible_inter
      (U j).isOpen pK.isOpenMap.isOpen_range (hU j) hp
    exact ⟨v, show pK v ∈ U j from hv.symm ▸ hx⟩
  obtain ⟨W, hW, hall⟩ := OriginalAffineSchemeDetectingOpen.exists_detecting_open
    (i ≫ f) (pK ≫ a) rK HK (pL ≫ c) rL HL U' hU'
  refine ⟨W.toScheme, W.ι ≫ pL, inferInstance, ?_, fun p hp ↦ ?_⟩
  · obtain ⟨x, hx⟩ := hW
    exact ⟨⟨x, hx⟩⟩
  · have hp' : (p ≫ W.ι) ≫ (pL ≫ c) = 𝟙 _ := by
      simpa only [Category.assoc] using hp
    have hm : Set.range (p ≫ W.ι) ⊆ W := by
      rintro _ ⟨x, rfl⟩
      exact (p x).property
    obtain ⟨z, hz, hd, hu⟩ := hall (p ≫ W.ι) hp' hm
    refine ⟨fun σ ↦ z σ ≫ pK, ?_, ?_, ?_⟩
    · intro σ
      rw [Category.assoc]
      exact hz σ
    · intro σ
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hd σ]
      simp only [Category.assoc, rL, pL, pullback.condition]
    · intro σ j x hx
      obtain ⟨v, rfl⟩ := hx
      exact hu σ j ⟨v, rfl⟩

end FLT.Mazur.OriginalSchemeDetectingOpen

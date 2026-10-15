/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalAffineSchemeOrbit
public import FLT.Mazur.OriginalGeometricallyIntegralOpen

/-!
# Original affine charts controlling arbitrary extended opens

Choose an affine chart of the original geometrically integral scheme. Its
extended open image meets every prescribed nonempty open. The constructed
algebraic point remains a whole morphism into that original chart, while all
its conjugates satisfy the unchanged larger-field conditions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OriginalAffineChartOrbit
set_option backward.isDefEq.respectTransparency false
variable {k L K : Type} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra L K] [Algebra k K] [IsScalarTower k L K]
  [Algebra.IsAlgebraic k L] [IsAlgClosed L]
  {X Y : Scheme} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [GeometricallyIntegral f]
  (a : Y ⟶ Spec (.of K)) (b : Y ⟶ X)
  (H : IsPullback a b (Spec.map (CommRingCat.ofHom (algebraMap k K))) f)

include H in
/-- One original affine chart contains an algebraic point whose whole orbit meets all opens. -/
theorem exists_chart_point_orbit {J : Type*} [Finite J]
    (U : J → Y.Opens) (hU : ∀ j, (U j : Set Y).Nonempty) :
    ∃ (W : Scheme) (i : W ⟶ X) (q : Spec (.of L) ⟶ W)
      (z : (L ≃ₐ[k] L) → (Spec (.of K) ⟶ Y)),
      IsAffine W ∧ IsOpenImmersion i ∧
      q ≫ i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L)) ∧
      (∀ σ, z σ ≫ a = 𝟙 _) ∧
      (∀ σ, z σ ≫ b = Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ q ≫ i) ∧
      ∀ σ j, Set.range (z σ) ⊆ U j := by
  let _ : IsIntegral Y := GeometricallyIntegral.geometrically_isIntegral _ _ _ H.flip
  obtain ⟨y⟩ := IsIntegral.nonempty (X := Y)
  let c := X.affineCover.idx (b y)
  let W := X.affineCover.X c
  let i := X.affineCover.f c
  obtain ⟨w, hw⟩ := X.affineCover.covers (b y)
  let _ : Nonempty W := ⟨w⟩
  let _ : GeometricallyIntegral (i ≫ f) :=
    OriginalGeometricallyIntegralOpen.geometricallyIntegral i f
  let Z := pullback i b
  let p : Z ⟶ Y := pullback.snd i b
  let r : Z ⟶ W := pullback.fst i b
  have H' : IsPullback (p ≫ a) r
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) (i ≫ f) :=
    (IsPullback.of_hasPullback i b).flip.paste_horiz H
  obtain ⟨v, _, _⟩ := Scheme.Pullback.exists_preimage_pullback w y hw
  have hp : (Set.range p).Nonempty := ⟨p v, v, rfl⟩
  let U' (j : J) : Z.Opens := p ⁻¹ᵁ U j
  have hU' (j : J) : (U' j : Set Z).Nonempty := by
    obtain ⟨x, hx, v, hv⟩ := nonempty_preirreducible_inter
      (U j).isOpen (p.isOpenMap.isOpen_range) (hU j) hp
    exact ⟨v, show p v ∈ U j from hv.symm ▸ hx⟩
  obtain ⟨q, z, hq, hz, he, hmem⟩ :=
    OriginalAffineSchemeOrbit.exists_point_orbit (L := L) (i ≫ f) (p ≫ a) r H' U' hU'
  refine ⟨W, i, q, fun σ ↦ z σ ≫ p, inferInstance, inferInstance, hq, ?_, ?_, ?_⟩
  · intro σ
    rw [Category.assoc]
    exact hz σ
  · intro σ
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, he σ]
    simp only [Category.assoc]
  · intro σ j x hx
    obtain ⟨v, rfl⟩ := hx
    exact hmem σ j ⟨v, rfl⟩

end FLT.Mazur.OriginalAffineChartOrbit

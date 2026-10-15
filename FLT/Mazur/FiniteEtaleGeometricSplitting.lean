/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteEtaleGeometricDisjointCover
public import FLT.Mazur.DisjointSectionCoverSplitting

/-!
# Constructed finite étale scheme splittings retaining geometric tests

The disjoint section cover gives an actual coproduct isomorphism of the
entire base change. Every sheet, the original finite étale square and the
whole geometric map are retained by explicit morphism identities.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteEtaleGeometricSplitting
universe u
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsFinite f] [IsAffine Y]
  {K : Type u} [Field K] [IsSepClosed K] (b : Spec (.of K) ⟶ Y)

/-- A finite étale scheme becomes an actual finite coproduct on a constructed étale neighborhood. -/
theorem exists_splitting :
    ∃ (n : ℕ) (U E : Scheme.{u}) (q : U ⟶ Y) (z : Spec (.of K) ⟶ U)
      (h : E ⟶ X) (p : E ⟶ U) (s : Fin n → (U ⟶ E))
      (e : (∐ fun _ : Fin n ↦ U) ≅ E),
      IsAffine U ∧ Etale q ∧ q.appTop.hom.FinitePresentation ∧ z ≫ q = b ∧
      IsPullback h p f q ∧ IsFinite p ∧ Etale p ∧
      (∀ i, s i ≫ p = 𝟙 U) ∧ (∀ i, IsOpenImmersion (s i)) ∧
      (∀ x : E, ∃ i, s i (p x) = x) ∧
      Pairwise (fun i j ↦ Disjoint (Set.range (s i)) (Set.range (s j))) ∧
      (∀ i, Sigma.ι (fun _ : Fin n ↦ U) i ≫ e.hom = s i) ∧
      e.hom ≫ p = Sigma.desc (fun _ : Fin n ↦ 𝟙 U) := by
  obtain ⟨n, U, E, q, z, h, p, s, hU, hq, hfp, hz, H, hp, he, hs, hi, hc, hd⟩ :=
    FiniteEtaleGeometricDisjointCover.exists_cover f b
  let _ (i : Fin n) : IsOpenImmersion (s i) := hi i
  refine ⟨n, U, E, q, z, h, p, s, DisjointSectionCoverSplitting.iso p s hc hd,
    hU, hq, hfp, hz, H, hp, he, hs, hi, hc, hd, ?_, ?_⟩
  · exact DisjointSectionCoverSplitting.ι_iso_hom p s hc hd
  · exact DisjointSectionCoverSplitting.iso_hom_base p s hc hd hs

end FLT.Mazur.FiniteEtaleGeometricSplitting

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanDirected
public import FLT.Mazur.PrincipalCoordinateIsomorphismRefinement

/-!
# Isomorphisms on several principal opens of a shared chart

First refine each leg to an isomorphism independently. Take the union of its
ambient source relations over the finite fan, then transport that exact
source enlargement through each isomorphism. The resulting isomorphisms use
one ambient relation set even when all their denominators are different.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A] {ι : Type v}
  {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
  [∀ i, Algebra.FiniteType R (B i)]
  {a : ι → A} {b : ∀ i, B i}
  (e : ∀ i, Localization.Away (a i) ≃ₐ[R] Localization.Away (b i))

/-- All existing isomorphisms survive any prescribed enlargement of the shared chart. -/
theorem exists_principalFan_bijective_source_extension
    (x : PrincipalFanStage a b (fun i ↦ (e i).toAlgHom))
    (hx : ∀ i, Function.Bijective (x.hom i))
    (s : Finset (relationIdeal R A)) (hs : x.source ≤ s) :
    ∃ y : PrincipalFanStage a b (fun i ↦ (e i).toAlgHom),
      x ≤ y ∧ y.source = s ∧ ∀ i, Function.Bijective (y.hom i) := by
  choose t ht d hd hfac using fun i ↦ exists_principal_equiv_source_extension (e i)
    (AlgEquiv.ofBijective (x.hom i) (hx i)) (x.fac i) hs
  exact ⟨⟨s, t, fun i ↦ (d i).toAlgHom, hfac⟩,
    ⟨hs, fun i ↦ ⟨hs, ht i, hd i⟩⟩, rfl, fun i ↦ (d i).bijective⟩

variable [Finite ι]

/-- Finitely many original principal isomorphisms descend with one shared ambient stage. -/
theorem exists_principalFan_bijective
    (x : PrincipalFanStage a b (fun i ↦ (e i).toAlgHom)) :
    ∃ y : PrincipalFanStage a b (fun i ↦ (e i).toAlgHom),
      x ≤ y ∧ ∀ i, Function.Bijective (y.hom i) := by
  classical
  let _ := Fintype.ofFinite ι
  choose z hxz hz using fun i ↦
    exists_principalMapStage_bijective (e i).bijective (principalFanLeg x i)
  let s := x.source ∪ Finset.univ.biUnion (fun i ↦ (z i).source)
  have hxs : x.source ≤ s := Finset.subset_union_left
  have hzs (i) : (z i).source ≤ s := by
    intro r hr
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hr⟩)
  choose t ht d hd hfac using fun i ↦ exists_principal_equiv_source_extension (e i)
    (AlgEquiv.ofBijective (z i).hom (hz i)) (z i).fac (hzs i)
  let y : PrincipalFanStage a b (fun i ↦ (e i).toAlgHom) :=
    ⟨s, t, fun i ↦ (d i).toAlgHom, hfac⟩
  refine ⟨y, ⟨hxs, fun i ↦ ?_⟩, fun i ↦ (d i).bijective⟩
  exact (hxz i).trans ⟨hzs i, ht i, hd i⟩

end FLT.Mazur.FiniteTypeRelationModel

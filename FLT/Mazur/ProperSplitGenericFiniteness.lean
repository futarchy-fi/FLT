/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProperDenseFiniteSections
public import FLT.Mazur.ProperPointExtension
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# A proper model with a dense finite split generic source is finite

Extend each of the finitely many original generic points by properness over a
valuation ring. Their closed section images cover the model by density, proving
finiteness without assuming any integral point lifts or finite flat closure.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.ProperSplitGenericFiniteness

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v
variable {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {X T : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]

/-- The actual generic point extends to a section, with its original coefficient map retained. -/
theorem exists_section (p : Spec (.of K) ⟶ X)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ s : Spec (.of R) ⟶ X,
      s ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s = p := by
  let sq : ValuativeCommSq f :=
    { R := R
      K := K
      i₁ := p
      i₂ := 𝟙 _
      commSq := ⟨by simpa only [Category.comp_id] using hp⟩ }
  have hc : ValuativeCriterion f := by
    have hf : IsProper f := inferInstance
    rw [IsProper.eq_valuativeCriterion] at hf
    exact hf.1.1.1
  obtain ⟨s, hg, hs⟩ := (hc.existence sq).exists_lift
  exact ⟨s, hs, hg⟩

/-- Finite generic rational points covering a dense source force the proper model to be finite. -/
theorem finite_of_split_dense (a : T ⟶ X) (ha : DenseRange a)
    {I : Type v} [Finite I] (p : I → (Spec (.of K) ⟶ T))
    (hp : ∀ j, p j ≫ a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (hcover : ∀ x : T, ∃ j : I, x ∈ Set.range (p j)) : IsFinite f := by
  choose s hs using fun j => exists_section f (p j ≫ a) (by
    simpa only [Category.assoc] using hp j)
  apply ProperDenseFiniteSections.finite_of_dense_sections f s (fun j => (hs j).1) a ha
  intro x
  obtain ⟨j, z, rfl⟩ := hcover x
  refine ⟨j, Spec.map (CommRingCat.ofHom (algebraMap R K)) z, ?_⟩
  exact congrArg (fun g : Spec (.of K) ⟶ X => g z) (hs j).2

/-- Over an algebraically closed generic field, finite generic schemes supply the point cover.
This uses only the underlying point cover and also applies to nonreduced generic schemes. -/
theorem finite_of_geometric_dense [IsAlgClosed K] (a : T ⟶ X) (ha : DenseRange a)
    (k : T ⟶ Spec (.of K)) [IsFinite k]
    (hk : a ≫ f = k ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) : IsFinite f := by
  let _ : IsLocallyArtinian T := IsLocallyArtinian.of_locallyQuasiFinite k
  let _ : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace k
  let _ : IsArtinianScheme T := ⟨⟩
  apply finite_of_split_dense f a ha (fun x : T => pointOfClosedPoint k x isClosed_singleton)
  · intro x
    rw [hk, pointOfClosedPoint_comp_assoc]
  · intro x
    exact ⟨x, IsLocalRing.closedPoint K, pointOfClosedPoint_apply k x _ _⟩

end FLT.Mazur.ProperSplitGenericFiniteness

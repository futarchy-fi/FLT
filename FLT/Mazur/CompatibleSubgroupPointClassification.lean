/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupIsoFaithful
public import FLT.Mazur.CompatibleSubgroupIsoBaseChange

/-!
# Restricting full comparison classifiers to the closed subgroup locus

A faithful subgroup condition and a monomorphic parameter inclusion restrict
an actual full-curve point classifier to a classifier of compatible comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S T X Y : Scheme} {n : ℕ} {E F : GeneralizedEllipticCurve S}
  (H : E.FiniteSubgroup n) (J : F.FiniteSubgroup n)
  (i : Y ⟶ X) (s : X ⟶ S) (t : T ⟶ S)
  (e : {f : T ⟶ X // f ≫ s = t} ≃ (E.baseChange t ≅ F.baseChange t))
  (hf : ∀ f : {f : T ⟶ X // f ≫ s = t},
    (∃ k : T ⟶ Y, k ≫ i = f.val) ↔
      ∃ a : CompatibleIso (H.baseChange t) (J.baseChange t), a.curve = e f)

/-- Forget the closed subgroup condition on the actual test map. -/
def subgroupTestForget (k : {k : T ⟶ Y // k ≫ i ≫ s = t}) :
    {f : T ⟶ X // f ≫ s = t} :=
  ⟨k.val ≫ i, (Category.assoc _ _ _).trans k.property⟩

/-- The factorization criterion constructs a compatible comparison on every closed-locus test. -/
def subgroupTestComparison (k : {k : T ⟶ Y // k ≫ i ≫ s = t}) :
    CompatibleIso (H.baseChange t) (J.baseChange t) :=
  ((hf (subgroupTestForget i s t k)).mp ⟨k.val, rfl⟩).choose

/-- The constructed comparison retains exactly the full comparison of its original test map. -/
theorem subgroupTestComparison_curve (k : {k : T ⟶ Y // k ≫ i ≫ s = t}) :
    (subgroupTestComparison H J i s t e hf k).curve = e (subgroupTestForget i s t k) :=
  ((hf (subgroupTestForget i s t k)).mp ⟨k.val, rfl⟩).choose_spec

variable [Mono i]

/-- Closed-locus tests classify every compatible comparison, including its full automorphism. -/
def subgroupTestPointEquiv :
    {k : T ⟶ Y // k ≫ i ≫ s = t} ≃ CompatibleIso (H.baseChange t) (J.baseChange t) :=
  Equiv.ofBijective (subgroupTestComparison H J i s t e hf) (by
    constructor
    · intro k l h
      apply Subtype.ext
      apply (cancel_mono i).mp
      have hc := congrArg CompatibleIso.curve h
      rw [subgroupTestComparison_curve, subgroupTestComparison_curve] at hc
      exact congrArg Subtype.val (e.injective hc)
    · intro a
      let f := e.symm a.curve
      obtain ⟨k, hk⟩ := (hf f).mpr ⟨a, (e.apply_symm_apply a.curve).symm⟩
      have hkt : k ≫ i ≫ s = t := by rw [← Category.assoc, hk]; exact f.property
      refine ⟨⟨k, hkt⟩, ?_⟩
      apply CompatibleIso.ext_curve
      rw [subgroupTestComparison_curve]
      have hforget : subgroupTestForget i s t ⟨k, hkt⟩ = f := Subtype.ext hk
      rw [hforget]
      exact e.apply_symm_apply a.curve)

/-- The restricted equivalence preserves the original full-curve classifier. -/
theorem subgroupTestPointEquiv_curve (k : {k : T ⟶ Y // k ≫ i ≫ s = t}) :
    (subgroupTestPointEquiv H J i s t e hf k).curve = e (subgroupTestForget i s t k) :=
  subgroupTestComparison_curve H J i s t e hf k

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CategoryDIntegralModels
public import FLT.GroupScheme.FiniteFlatExtensionKernelIso
public import FLT.GroupScheme.IntegralSimpleSubobject

/-!
# Integral composition series with canonical factors

Recursion on the point order produces a composition series by actual integral
extensions. Simple kernels are identified with the constant-three or cube-root
model, and their integral isomorphisms transport every torsor field. The simple
classification remains an explicit hypothesis, with a separate specialization
to the augmented discriminant bound.

The series is recorded from the bottom simple kernel upward through successive
quotients. Its two kinds of factors are not yet sorted.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- An integral composition series with canonical factors, recorded by successive
simple kernels and their integral quotient models. -/
inductive HasCanonicalCompositionSeries : FiniteFlatObject ZInvTwo → Prop
  /-- A trivial integral model terminates the series. -/
  | zero {H : FiniteFlatObject ZInvTwo}
      (e : H.model.CoordinateRing ≃ₐ[ZInvTwo] ZInvTwo) : HasCanonicalCompositionSeries H
  /-- A constant-three kernel followed by the series of the integral quotient. -/
  | constant {H Q : FiniteFlatObject ZInvTwo}
      (E : FiniteFlatExtension constantThree H Q)
      (hQ : HasCanonicalCompositionSeries Q) : HasCanonicalCompositionSeries H
  /-- A cube-root kernel followed by the series of the integral quotient. -/
  | multiplicative {H Q : FiniteFlatObject ZInvTwo}
      (E : FiniteFlatExtension muThree H Q)
      (hQ : HasCanonicalCompositionSeries Q) : HasCanonicalCompositionSeries H

/-- Classification of simple category-D models produces a genuine integral
composition series, retaining exactness and torsors at every stage. -/
theorem canonicalCompositionSeriesExists
    (hclass : ∀ A : FiniteFlatObject ZInvTwo, Simple A → InCategoryD A →
      Nonempty (A.Iso constantThree) ∨ Nonempty (A.Iso muThree))
    (H : FiniteFlatObject ZInvTwo) (hD : InCategoryD H) :
    HasCanonicalCompositionSeries H := by
  suffices h : ∀ n : ℕ, ∀ J : FiniteFlatObject ZInvTwo, Nat.card J.points = n →
      InCategoryD J → HasCanonicalCompositionSeries J from h _ H rfl hD
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro J hn hJ
    by_cases hz : Subsingleton J.points
    · let subsingletonJ : Subsingleton J.points := hz
      exact .zero J.zeroCoordinatesEquiv
    · let nontrivialJ : Nontrivial J.points := not_subsingleton_iff_nontrivial.mp hz
      obtain ⟨A, Q, E, hs, hlt⟩ := J.existsSimpleKernel
      have hQ := ih (Nat.card Q.points) (hlt.trans_eq hn) Q rfl (E.inCategoryDRight hJ)
      rcases hclass A hs (E.inCategoryDLeft hJ) with he | he
      · exact .constant (E.transportKernel he.some) hQ
      · exact .multiplicative (E.transportKernel he.some) hQ

/-- The augmented discriminant bounds for simple category-D models suffice
for the integral composition series; no reverse extension hypothesis is needed. -/
theorem canonicalCompositionSeriesOfDiscriminantBounds
    (hdisc : ∀ A : FiniteFlatObject ZInvTwo, Simple A → InCategoryD A →
      AugmentedDiscriminantBound A)
    (H : FiniteFlatObject ZInvTwo) (hD : InCategoryD H) :
    HasCanonicalCompositionSeries H :=
  canonicalCompositionSeriesExists
    (fun A hs hA ↦ hs.integral_model_of_discriminantBound hA (hdisc A hs hA)) H hD

end ThreeAdicPlan

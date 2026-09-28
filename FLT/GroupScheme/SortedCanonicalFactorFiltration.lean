/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.AdjacentCanonicalFactors
public import FLT.GroupScheme.CanonicalFactorFiltration

/-!
# Sorting canonical integral factor filtrations

Adjacent interchange moves every multiplicative factor below the constant
factors. Composition assembles the boundary into one integral extension. The
only arithmetic input to existence is the stated discriminant bound for simple
category-D models.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- Move one multiplicative factor below a block of constant factors. -/
theorem HasFactorFiltration.bubbleMultiplicativeFactor
    (n : ℕ) {H : FiniteFlatObject ZInvTwo} {rest : List (FiniteFlatObject ZInvTwo)}
    (hF : HasFactorFiltration H (muThree :: (List.replicate n constantThree ++ rest))) :
    HasFactorFiltration H (List.replicate n constantThree ++ muThree :: rest) := by
  induction n generalizing H with
  | zero => simpa using hF
  | succ n ih =>
    have h : HasFactorFiltration H
        (muThree :: constantThree :: (List.replicate n constantThree ++ rest)) := by
      simpa only [List.replicate_succ, List.cons_append] using hF
    cases h with
    | extension E₂ hB =>
      cases hB with
      | extension E₁ hA =>
        obtain ⟨B', ⟨F⟩, ⟨G⟩⟩ := swapAdjacentFactors E₁ E₂
        simpa only [List.replicate_succ, List.cons_append] using
          HasFactorFiltration.extension G (ih (.extension F hA))

/-- A canonical factor list can be sorted without changing its integral middle model. -/
theorem HasFactorFiltration.sortCanonicalFactors
    {H : FiniteFlatObject ZInvTwo} {factors : List (FiniteFlatObject ZInvTwo)}
    (hF : HasFactorFiltration H factors)
    (hfactors : ∀ Q ∈ factors, Q = constantThree ∨ Q = muThree) :
    ∃ n m : ℕ, HasFactorFiltration H
      (List.replicate n constantThree ++ List.replicate m muThree) := by
  induction hF with
  | zero e => exact ⟨0, 0, .zero e⟩
  | @extension A H Q factors E hA ih =>
    obtain ⟨n, m, hsort⟩ := ih (fun J hJ ↦ hfactors J (by simp [hJ]))
    rcases hfactors Q (by simp) with rfl | rfl
    · exact ⟨n + 1, m, by
        simpa only [List.replicate_succ, List.cons_append] using
          HasFactorFiltration.extension E hsort⟩
    · refine ⟨n, m + 1, ?_⟩
      simpa only [List.replicate_succ] using
        HasFactorFiltration.bubbleMultiplicativeFactor n (.extension E hsort)

/-- The identity subgroup has a full integral extension with trivial quotient. -/
theorem FiniteFlatObject.existsIdentityExtension (H : FiniteFlatObject ZInvTwo) :
    ∃ Q : FiniteFlatObject ZInvTwo, ∃ _ : FiniteFlatExtension H H Q,
      Nonempty (Q.model.CoordinateRing ≃ₐ[ZInvTwo] ZInvTwo) := by
  let f : H.Hom H := BialgHom.id ZInvTwo H.model.CoordinateRing
  let i : GenericGaloisHom H.toFF H.toFF := genericHom (X := H.toFF) (Y := H.toFF) f
  have hi : Function.Injective i := by
    intro a b hab
    exact (genericHom_id H.toFF a).symm.trans (hab.trans (genericHom_id H.toFF b))
  obtain ⟨T, q, hq, hexact, _⟩ := i.exists_exact_quotient
  let Q := (q.flatQuotient hq).toFiniteFlatObject
  let E : FiniteFlatExtension H H Q :=
    FiniteFlatObject.extensionOfClosedImmersion f hi Function.surjective_id q hq hexact
  have hz (t : T.Points) : t = 0 := by
    obtain ⟨h, rfl⟩ := hq t
    exact (hexact h).mpr ⟨h, genericHom_id H.toFF h⟩
  let quotientSubsingleton : Subsingleton Q.points := ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
  exact ⟨Q, E, ⟨Q.zeroCoordinatesEquiv⟩⟩

/-- A sorted factor list assembles into the integral extension at its boundary. -/
theorem sortedExtensionOfConstantThenMultiplicative
    (n m : ℕ) {H : FiniteFlatObject ZInvTwo}
    (hF : HasFactorFiltration H
      (List.replicate n constantThree ++ List.replicate m muThree)) :
    Nonempty (SortedFiniteFlatExtension H) := by
  induction n generalizing H with
  | zero =>
    have hm : HasFiltration H muThree := hF.ofAllEqual (by
      intro J hJ
      have hJ' : J ∈ List.replicate m muThree := by simpa using hJ
      exact (List.mem_replicate.mp hJ').2)
    obtain ⟨Q, E, ⟨eQ⟩⟩ := H.existsIdentityExtension
    exact ⟨{
      left := H
      right := Q
      extension := E
      leftFiltration := hm
      rightFiltration := .zero eQ }⟩
  | succ n ih =>
    have h : HasFactorFiltration H
        (constantThree :: (List.replicate n constantThree ++ List.replicate m muThree)) := by
      simpa only [List.replicate_succ, List.cons_append] using hF
    cases h with
    | extension E hA =>
      obtain ⟨S⟩ := ih hA
      obtain ⟨T, F, G, _, _, _⟩ := composeIntegralExtensionsCompatible S.extension E
      exact ⟨{
        left := S.left
        right := T
        extension := F
        leftFiltration := S.leftFiltration
        rightFiltration := .extension G S.rightFiltration }⟩

/-- Every canonical integral factor filtration has an actual sorted integral extension. -/
theorem sortedExtensionOfCanonicalFactorFiltration
    {H : FiniteFlatObject ZInvTwo} {factors : List (FiniteFlatObject ZInvTwo)}
    (hF : HasFactorFiltration H factors)
    (hfactors : ∀ Q ∈ factors, Q = constantThree ∨ Q = muThree)
    (_hkill : KilledByQ 3 H) : Nonempty (SortedFiniteFlatExtension H) := by
  obtain ⟨n, m, hsort⟩ := hF.sortCanonicalFactors hfactors
  exact sortedExtensionOfConstantThenMultiplicative n m hsort

/-- Discriminant bounds for simple category-D models give a sorted integral extension. -/
theorem sortedExtensionExists
    (hdisc : ∀ A : FiniteFlatObject ZInvTwo,
      Simple A → InCategoryD A → AugmentedDiscriminantBound A)
    (H : FiniteFlatObject ZInvTwo) (hD : InCategoryD H) (hkill : KilledByQ 3 H) :
    Nonempty (SortedFiniteFlatExtension H) := by
  obtain ⟨factors, hF, hfactors⟩ := canonicalFactorFiltrationOfDiscriminantBounds hdisc H hD
  exact sortedExtensionOfCanonicalFactorFiltration hF hfactors hkill

end ThreeAdicPlan

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicCompatibleImages
public import FLT.Mazur.IdealAdicFormalInjectivity

/-!
# Completion for a cofinal cohomology image filtration

Reverse containment constructs adic coordinates from sufficiently deep image
quotients. Compatibility makes these coordinates independent of the chosen depth.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.IdealAdicQuotient

/-- Two paths of identity-induced quotient maps with the same endpoints agree. -/
lemma quotientMap_identity_diamond {A : Type*} [CommRing A]
    {V : Type*} [AddCommGroup V] [Module A V]
    (P Q S T : Submodule A V) (hPQ : P ≤ Q) (hPS : P ≤ S)
    (hQT : Q ≤ T) (hST : S ≤ T) (x : V ⧸ P) :
    Q.mapQ T LinearMap.id hQT (P.mapQ Q LinearMap.id hPQ x) =
      S.mapQ T LinearMap.id hST (P.mapQ S LinearMap.id hPS x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ z => rfl

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation] (J : Ideal R)

attribute [local irreducible] cohomologyImage

/-- Reverse containment descends a deep image quotient to an ordinary adic quotient. -/
def imageToAdicQuotient (q : ℕ) {a b : ℕ}
    (h : cohomologyImage ρ I M q b ≤ J ^ a • (⊤ : Submodule R (ModuleRingH ρ M q))) :
    imageQuotient ρ I M q b →ₗ[R]
      ModuleRingH ρ M q ⧸ (J ^ a • ⊤ : Submodule R (ModuleRingH ρ M q)) :=
  (cohomologyImage ρ I M q b).mapQ _ LinearMap.id h

/-- Any two depths with the same reverse containment give the same adic coordinate. -/
lemma imageToAdicQuotient_independent (q : ℕ) (y : compatibleImages ρ I M q)
    {a b c : ℕ}
    (hb : cohomologyImage ρ I M q b ≤ J ^ a • (⊤ : Submodule R (ModuleRingH ρ M q)))
    (hc : cohomologyImage ρ I M q c ≤ J ^ a • (⊤ : Submodule R (ModuleRingH ρ M q))) :
    imageToAdicQuotient ρ I M J q hb (y.val b) =
      imageToAdicQuotient ρ I M J q hc (y.val c) := by
  let d := max b c
  calc
    _ = imageToAdicQuotient ρ I M J q hb
        (imageQuotientReduction ρ I M q (Nat.le_max_left b c) (y.val d)) :=
      congrArg (imageToAdicQuotient ρ I M J q hb)
        (y.property b d (Nat.le_max_left b c)).symm
    _ = imageToAdicQuotient ρ I M J q hc
        (imageQuotientReduction ρ I M q (Nat.le_max_right b c) (y.val d)) :=
      quotientMap_identity_diamond _ _ _ _
        (cohomologyImage_antitone ρ I M q (Nat.le_max_left b c))
        (cohomologyImage_antitone ρ I M q (Nat.le_max_right b c)) hb hc (y.val d)
    _ = _ := congrArg (imageToAdicQuotient ρ I M J q hc)
      (y.property c d (Nat.le_max_right b c))

variable (hJ : ∀ (r : R), r ∈ J → ∀ U : X.affineOpens,
  X.presheaf.map U.1.leTop.op (ρ r) ∈ I.ideal U)

/-- Cofinality supplies a completed class for every compatible image-quotient family. -/
theorem completionToImages_surjective_of_cofinal (q : ℕ)
    (h : ∀ n, ∃ m, n ≤ m ∧ cohomologyImage ρ I M q m ≤
      J ^ n • (⊤ : Submodule R (ModuleRingH ρ M q))) :
    Function.Surjective (completionToImages ρ I M J hJ q) := by
  choose m hnm hm using h
  intro y
  let x := fun n ↦ imageToAdicQuotient ρ I M J q (hm n) (y.val (m n))
  have hx : ∀ {a b : ℕ} (hab : a ≤ b),
      AdicCompletion.transitionMap J (ModuleRingH ρ M q) hab (x b) = x a := by
    intro a b hab
    have hb := (hm b).trans (Submodule.pow_smul_top_le J (ModuleRingH ρ M q) hab)
    calc
      _ = imageToAdicQuotient ρ I M J q hb (y.val (m b)) := by
        dsimp only [x]
        induction y.val (m b) using Submodule.Quotient.induction_on with
        | _ z => rfl
      _ = x a := imageToAdicQuotient_independent ρ I M J q y hb (hm a)
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  funext n
  change adicToImageQuotient ρ I M J hJ q n
    (imageToAdicQuotient ρ I M J q (hm n) (y.val (m n))) = y.val n
  rw [← y.property n (m n) (hnm n)]
  induction y.val (m n) using Submodule.Quotient.induction_on with
  | _ z => rfl

/-- The canonical map to image quotients is an isomorphism for cofinal filtrations. -/
theorem completionToImages_bijective_of_cofinal (q : ℕ)
    (h : ∀ n, ∃ m, n ≤ m ∧ cohomologyImage ρ I M q m ≤
      J ^ n • (⊤ : Submodule R (ModuleRingH ρ M q))) :
    Function.Bijective (completionToImages ρ I M J hJ q) := by
  refine ⟨?_, completionToImages_surjective_of_cofinal ρ I M J hJ q h⟩
  intro x y hxy
  apply formalComparison_injective_of_cofinal ρ I M J hJ q h
  simpa only [compatibleImageComparison_completionToImages] using
    congrArg (compatibleImageComparison ρ I M q) hxy

/-- The actual completion identifies linearly with compatible image quotients. -/
def imageCompletionEquiv (q : ℕ)
    (h : ∀ n, ∃ m, n ≤ m ∧ cohomologyImage ρ I M q m ≤
      J ^ n • (⊤ : Submodule R (ModuleRingH ρ M q))) :
    AdicCompletion J (ModuleRingH ρ M q) ≃ₗ[R] compatibleImages ρ I M q :=
  LinearEquiv.ofBijective (completionToImages ρ I M J hJ q)
    (completionToImages_bijective_of_cofinal ρ I M J hJ q h)

end FLT.Mazur.IdealAdicQuotient

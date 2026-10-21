/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryRelationSupport
public import FLT.Mazur.OriginalBoundaryResidualPrincipalCover

/-!
# Residual boundary lifting from open equations on the full relation

At each remaining original scalar prime, a raw lift and a solved arrow open
suffice if the closed bad-arrow image avoids that prime. The principal lifts
are constructed, not supplied. These point-dependent tests keep both bad
source-image closures and all full boundary and mixed relation equations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections SchemeOpenEnvelope SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [IsAffine A] (e : CategoryTheory.EquivalenceRelation p q)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : compatibleFunctions (pullback.snd p J.subschemeι)
    (InvariantIdealRelation.snd J p q hJ))
local notation "σ" => (Subring.subtype (compatibleFunctions p q))
local notation "σD" => p.appTop.hom.comp (Subring.subtype (compatibleFunctions p q))

include e hf in
/-- Raw full-relation tests only on the residual intersection control exact original support. -/
theorem originalBoundaryLift_support_of_residual_relation_cover
    (Q : Ideal (compatibleFunctions p q))
    (hraw : ∀ x : PrimeSpectrum (compatibleFunctions p q),
      x ∈ closure (scalarMorphism σ '' (J.support : Set A)) ∩
        closure (scalarMorphism σ '' (finiteTargetOpen p : Set A)ᶜ) →
      x ∉ PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) →
      ∃ (a : Γ(A, ⊤)) (O : D.Opens), J.subschemeι.appTop a = t.val ∧
        O.ι.appTop (p.appTop a) = O.ι.appTop (q.appTop a) ∧
        x ∉ closure (scalarMorphism σD '' (O : Set D)ᶜ)) :
    PrimeSpectrum.zeroLocus
        (originalBoundaryLiftIdeal (p := p) (q := q) J t.val :
          Set (compatibleFunctions p q)) ⊆
      PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) := by
  let _ := QuasiCompact.compactSpace_of_compactSpace p
  let _ := quasiSeparatedSpace_of_quasiSeparated p
  apply originalBoundaryLift_support_of_residual_principal_cover e J hJ f hf t Q
  intro x hx hxQ
  obtain ⟨a, O, ha, he, hO⟩ := hraw x hx hxQ
  exact exists_principalBoundaryLift_off_relation_image J t.val a ha O he x hO

include e hf in
/-- A residual cover by solved raw arrow equations constructs an unscaled original lift. -/
theorem exists_originalBoundaryLift_of_residual_relation_cover
    (hraw : ∀ x : PrimeSpectrum (compatibleFunctions p q),
      x ∈ closure (scalarMorphism σ '' (J.support : Set A)) ∩
        closure (scalarMorphism σ '' (finiteTargetOpen p : Set A)ᶜ) →
      ∃ (a : Γ(A, ⊤)) (O : D.Opens), J.subschemeι.appTop a = t.val ∧
        O.ι.appTop (p.appTop a) = O.ι.appTop (q.appTop a) ∧
        x ∉ closure (scalarMorphism σD '' (O : Set D)ᶜ)) :
    ∃ w : compatibleFunctions p q, J.subschemeι.appTop w.val = t.val := by
  let _ := QuasiCompact.compactSpace_of_compactSpace p
  let _ := quasiSeparatedSpace_of_quasiSeparated p
  apply exists_originalBoundaryLift_of_residual_principal_cover e J hJ f hf t
  intro x hx
  obtain ⟨a, O, ha, he, hO⟩ := hraw x hx
  exact exists_principalBoundaryLift_off_relation_image J t.val a ha O he x hO

end FLT.Mazur.EquivalenceRelationOrderedFrames

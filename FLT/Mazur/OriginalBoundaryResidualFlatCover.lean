/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryFlatRelationLift
public import FLT.Mazur.OriginalBoundaryResidualPrincipalCover

/-!
# Residual original boundary support from full flat branch equations

Only the intersection of the two original bad source-image closures needs
branch solutions. Each point may use its own branch neighborhood and raw
numerator. The branch need not cover the entire scalar spectrum, and no
closedness of the original arrow scalar map is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections SchemeOpenEnvelope SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S Y : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [IsAffine A] (e : CategoryTheory.EquivalenceRelation p q)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : compatibleFunctions (pullback.snd p J.subschemeι)
    (InvariantIdealRelation.snd J p q hJ))
local notation "σ" => (Subring.subtype (compatibleFunctions p q))
local notation "σD" => p.appTop.hom.comp (Subring.subtype (compatibleFunctions p q))
variable (g : Y ⟶ Spec (.of (compatibleFunctions p q)))
  [Flat g] [LocallyOfFinitePresentation g]
local notation "π" => scalarMorphism σD
local notation "k" => pullback.fst π g
local notation "h" => pullback.snd π g

include e hf in
/-- Full flat branch equations at residual original primes bound the exact original support. -/
theorem originalBoundaryLift_support_of_residual_flat_cover
    (Q : Ideal (compatibleFunctions p q))
    (hraw : ∀ x : PrimeSpectrum (compatibleFunctions p q),
      x ∈ closure (scalarMorphism σ '' (J.support : Set A)) ∩
        closure (scalarMorphism σ '' (finiteTargetOpen p : Set A)ᶜ) →
      x ∉ PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) →
      ∃ (y : Y) (V : Y.Opens) (a : Γ(A, ⊤)), g y = x ∧ y ∈ V ∧
        J.subschemeι.appTop a = t.val ∧
        (pullback π g : Scheme).presheaf.map
          (homOfLE le_top : h ⁻¹ᵁ V ⟶ ⊤).op
            ((k).appTop (p.appTop a - q.appTop a)) = 0) :
    PrimeSpectrum.zeroLocus
        (originalBoundaryLiftIdeal (p := p) (q := q) J t.val :
          Set (compatibleFunctions p q)) ⊆
      PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)) := by
  let _ := QuasiCompact.compactSpace_of_compactSpace p
  let _ := quasiSeparatedSpace_of_quasiSeparated p
  apply originalBoundaryLift_support_of_residual_principal_cover e J hJ f hf t Q
  intro x hx hxQ
  obtain ⟨y, V, a, hxy, hy, ha, he⟩ := hraw x hx hxQ
  obtain ⟨s, hs, u, hu⟩ :=
    exists_principalBoundaryLift_of_flat_relation_branch g V J t.val a ha y hy he
  exact ⟨s, hxy ▸ hs, u, hu⟩

include e hf in
/-- A full residual flat branch cover constructs an unscaled original invariant boundary lift. -/
theorem exists_originalBoundaryLift_of_residual_flat_cover
    (hraw : ∀ x : PrimeSpectrum (compatibleFunctions p q),
      x ∈ closure (scalarMorphism σ '' (J.support : Set A)) ∩
        closure (scalarMorphism σ '' (finiteTargetOpen p : Set A)ᶜ) →
      ∃ (y : Y) (V : Y.Opens) (a : Γ(A, ⊤)), g y = x ∧ y ∈ V ∧
        J.subschemeι.appTop a = t.val ∧
        (pullback π g : Scheme).presheaf.map
          (homOfLE le_top : h ⁻¹ᵁ V ⟶ ⊤).op
            ((k).appTop (p.appTop a - q.appTop a)) = 0) :
    ∃ w : compatibleFunctions p q, J.subschemeι.appTop w.val = t.val := by
  let _ := QuasiCompact.compactSpace_of_compactSpace p
  let _ := quasiSeparatedSpace_of_quasiSeparated p
  apply exists_originalBoundaryLift_of_residual_principal_cover e J hJ f hf t
  intro x hx
  obtain ⟨y, V, a, hxy, hy, ha, he⟩ := hraw x hx
  obtain ⟨s, hs, u, hu⟩ :=
    exists_principalBoundaryLift_of_flat_relation_branch g V J t.val a ha y hy he
  exact ⟨s, hxy ▸ hs, u, hu⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames

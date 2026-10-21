/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryScalarRelation
public import FLT.Mazur.InvariantIdealRelationMonomorphism
public import FLT.Mazur.SchemeRelationScalarMonomorphism

/-!
# The original full boundary embeds in its scalar-image kernel

The original equivalence relation supplies monicity on the entire boundary
after every scalar base change. Etale image geometry then constructs an open
immersion; surjectivity identifies the full relation, including nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars FlatScalarSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme.{0}} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
local notation "R" => invariants p.appTop.hom q.appTop.hom
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
variable (S : Type) [CommRing S] [Algebra (invariants p.appTop.hom q.appTop.hom) S]
local notation "b" => base R S J.subscheme
local notation "c" => SchemeScalarImageQuotient.projection b

include e in
/-- The entire original boundary relation remains monic after changing scalar base. -/
theorem originalBoundaryKernelComparison_mono :
    Mono (originalBoundaryKernelComparison p q J hJ S) := by
  let _ : JointlyMono₂ p q := e.toJointlyMono₂
  dsimp only [originalBoundaryKernelComparison]
  infer_instance

include e in
/-- Etale scalar-image geometry embeds the whole original boundary as an open subscheme. -/
theorem originalBoundaryKernelComparison_isOpenImmersion [Etale p] [Etale c] :
    IsOpenImmersion (originalBoundaryKernelComparison p q J hJ S) := by
  let _ : JointlyMono₂ p q := e.toJointlyMono₂
  dsimp only [base, originalBoundaryKernelComparison] at *
  exact SchemeRelationScalarBaseChange.kernelComparison_isOpenImmersion
    (pullback.snd p J.subschemeι) (InvariantIdealRelation.snd J p q hJ) _
    (originalBoundary_scalar_condition p q J hJ) (algebraMap R S)

include e in
/-- Surjectivity identifies the actual original boundary relation with the full kernel pair. -/
theorem originalBoundaryKernelComparison_isIso [Etale p] [Etale c]
    [Surjective (originalBoundaryKernelComparison p q J hJ S)] :
    IsIso (originalBoundaryKernelComparison p q J hJ S) := by
  let _ := originalBoundaryKernelComparison_isOpenImmersion e J hJ S
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames

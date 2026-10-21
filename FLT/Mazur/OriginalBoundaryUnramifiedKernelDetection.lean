/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryRankStageDenseCoverage
public import FLT.Mazur.OriginalBoundaryUnramifiedEndpointEquations
public import FLT.Mazur.SchemeInfinitesimalPointDetection

/-!
# Full nonreduced comparison equations from image rigidity and point coverage

Every infinitesimal point test has constant original rank, so its entire
endpoint source is finite. The constructed nonreduced lifts annihilate the
full original comparison kernel at every stalk order. Noetherian adic
separation then kills that kernel on the unchanged coefficient scheme.
No global finite endpoint or invariant-ring Noetherianity is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeInfinitesimalPointDetection SchemeScalarImageQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem kernel_le_of_infinitesimal_tests {C T B : Scheme.{0}}
    [IsLocallyNoetherian B] (c : C ⟶ T) (t : B ⟶ T)
    (h : ∀ (u : B) (k : ℕ), RingHom.ker c.appTop.hom ≤
      RingHom.ker (pointThickeningMap B u k ≫ t).appTop.hom) :
    RingHom.ker c.appTop.hom ≤ RingHom.ker t.appTop.hom := by
  intro r hr
  change t.appTop r = 0
  apply section_eq_zero B
  intro u k
  exact h u k hr

private theorem finite_infinitesimal_endpoint {A B : Scheme.{0}} (E : Over A)
    [Etale E.hom] [IsSeparated E.hom] [QuasiCompact E.hom] [LocallyQuasiFinite E.hom]
    (b : B ⟶ A) (u : B) (k : ℕ) :
    IsFinite (pullback.snd E.hom (pointThickeningMap B u k ≫ b)) := by
  obtain ⟨n, hn⟩ := exists_exactRank E (b u)
  apply finite_pullback_of_exactRank E n
  rintro _ ⟨v, rfl⟩
  change b (pointThickeningMap B u k v) ∈ exactRank E n
  rw [pointThickeningMap_apply]
  exact hn

private theorem dense_test_of_coverage {C T B U : Scheme.{0}}
    (c : C ⟶ T) (t : B ⟶ T) (h : Set.range t ⊆ Set.range c) (a : U ⟶ B) :
    Dense ((a ≫ t) ⁻¹' Set.range c) := by
  have he : (a ≫ t) ⁻¹' Set.range c = Set.univ :=
    Set.eq_univ_of_forall (fun v ↦ h (Set.mem_range_self (a v)))
  rw [he]
  exact dense_univ

private theorem point_test_noetherian {B : Scheme.{0}} [IsLocallyNoetherian B]
    (u : B) (k : ℕ) : IsNoetherian (pointThickening B u k) := by
  unfold pointThickening
  infer_instance

variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A]
  [Etale p] [IsSeparated p] [QuasiCompact p] [LocallyQuasiFinite p]
  [IsLocallyNoetherian B]
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local instance kernelDetectionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance kernelDetectionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance kernelDetectionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local instance kernelDetectionOver_quasiFinite : LocallyQuasiFinite (Over.mk p).hom :=
  ‹LocallyQuasiFinite p›
local instance kernelDetectionBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
local notation "x" => pullback.fst f f ≫ J.subschemeι
attribute [local irreducible] scalarMorphism

include e

/-- Full endpoint finiteness is constructed on every actual infinitesimal coefficient test. -/
theorem originalBoundary_kernel_zero_of_unramified_image_coverage
    [FormallyUnramified (projection f)] (t : B ⟶ pullback f f)
    (h : Set.range t ⊆ Set.range c) :
    RingHom.ker (c).appTop.hom ≤ RingHom.ker t.appTop.hom := by
  apply kernel_le_of_infinitesimal_tests c t
  intro u k
  let _ := point_test_noetherian u k
  let _ : IsFinite (pullback.snd p ((pointThickeningMap B u k ≫ t) ≫ x)) := by
    rw [Category.assoc]
    exact finite_infinitesimal_endpoint (Over.mk p) (t ≫ x) u k
  exact originalBoundary_full_kernel_of_unramified_image e J hJ
    (pointThickeningMap B u k ≫ t) (dense_test_of_coverage c t h _)

/-- Dense original coverage at one rank order suffices for every nonreduced coefficient order. -/
theorem originalBoundary_full_kernel_of_dense_rankStages
    [FormallyUnramified (projection f)] (t : B ⟶ pullback f f) (k : ℕ)
    (h : ∀ n, Dense ((rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t) ⁻¹' Set.range c)) :
    RingHom.ker (c).appTop.hom ≤ RingHom.ker t.appTop.hom :=
  originalBoundary_kernel_zero_of_unramified_image_coverage e J hJ t
    (originalBoundary_coverage_of_dense_rankStages J hJ t k h)

end FLT.Mazur.EquivalenceRelationOrderedFrames

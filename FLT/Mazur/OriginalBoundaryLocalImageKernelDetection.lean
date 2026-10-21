/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryRankStageDenseCoverage
public import FLT.Mazur.OriginalBoundaryUnramifiedOpenLift
public import FLT.Mazur.SchemeInfinitesimalPointDetection

/-!
# Full original equations from pointwise image rigidity

Each coefficient point may choose its own unramified open around the second
endpoint. All infinitesimal neighborhoods of that point land in this open.
Finite endpoint tests and adic separation detect the full nonreduced kernel;
no global rigidity or finite endpoint source is assumed.
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

private theorem point_test_range {B Y : Scheme.{0}} (a : B ⟶ Y)
    (u : B) (k : ℕ) (U : Y.Opens) (hu : a u ∈ U) :
    Set.range (pointThickeningMap B u k ≫ a) ⊆ U := by
  rintro _ ⟨v, rfl⟩
  change a (pointThickeningMap B u k v) ∈ U
  rwa [pointThickeningMap_apply]

private theorem kernel_le_of_local_tests {C T B X S : Scheme.{0}}
    [IsLocallyNoetherian B] (c : C ⟶ T) (t : B ⟶ T) (y : T ⟶ X) (f : X ⟶ S)
    (hU : ∀ u : B, ∃ U : X.Opens,
      (t ≫ y) u ∈ U ∧ FormallyUnramified (U.ι ≫ f))
    (h : ∀ (u : B) (k : ℕ) (U : X.Opens), FormallyUnramified (U.ι ≫ f) →
      (t ≫ y) u ∈ U →
      RingHom.ker c.appTop.hom ≤ RingHom.ker (pointThickeningMap B u k ≫ t).appTop.hom) :
    RingHom.ker c.appTop.hom ≤ RingHom.ker t.appTop.hom := by
  apply kernel_le_of_infinitesimal_tests c t
  intro u k
  obtain ⟨U, hu, hU⟩ := hU u
  exact h u k U hU hu

variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A]
  [Etale p] [IsSeparated p] [QuasiCompact p] [LocallyQuasiFinite p]
  [IsLocallyNoetherian B]
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local instance localKernelDetectionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance localKernelDetectionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance localKernelDetectionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local instance localKernelDetectionOver_quasiFinite : LocallyQuasiFinite (Over.mk p).hom :=
  ‹LocallyQuasiFinite p›
local instance localKernelDetectionBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
local notation "x" => pullback.fst f f ≫ J.subschemeι
attribute [local irreducible] scalarMorphism Scheme.IdealSheafData.subscheme

include e

private theorem point_kernel_of_unramified_open
    (t : B ⟶ pullback f f) (h : Set.range t ⊆ Set.range c)
    (u : B) (k : ℕ) (U : J.subscheme.Opens)
    [FormallyUnramified (U.ι ≫ projection f)]
    (hu : (t ≫ pullback.snd f f) u ∈ U) :
    RingHom.ker (c).appTop.hom ≤ RingHom.ker (pointThickeningMap B u k ≫ t).appTop.hom := by
  let _ := point_test_noetherian u k
  let _ : IsFinite (pullback.snd p ((pointThickeningMap B u k ≫ t) ≫ x)) := by
    rw [Category.assoc]
    exact finite_infinitesimal_endpoint (Over.mk p) (t ≫ x) u k
  apply originalBoundary_full_kernel_of_unramified_open e J hJ U
    (pointThickeningMap B u k ≫ t) (dense_test_of_coverage c t h _)
  simpa only [Category.assoc] using point_test_range (t ≫ pullback.snd f f) u k U hu

/-- Full endpoint finiteness is constructed on every actual infinitesimal coefficient test. -/
theorem originalBoundary_kernel_zero_of_local_image_coverage
    (t : B ⟶ pullback f f)
    (hU : ∀ u : B, ∃ U : J.subscheme.Opens,
      (t ≫ pullback.snd f f) u ∈ U ∧ FormallyUnramified (U.ι ≫ projection f))
    (h : Set.range t ⊆ Set.range c) :
    RingHom.ker (c).appTop.hom ≤ RingHom.ker t.appTop.hom := by
  apply kernel_le_of_local_tests c t (pullback.snd f f) (projection f) hU
  intro u k U hF hu
  let _ := hF
  exact point_kernel_of_unramified_open e J hJ t h u k U hu

/-- Dense original coverage at one rank order suffices for every nonreduced coefficient order. -/
theorem originalBoundary_full_kernel_of_local_dense_rankStages
    (t : B ⟶ pullback f f)
    (hU : ∀ u : B, ∃ U : J.subscheme.Opens,
      (t ≫ pullback.snd f f) u ∈ U ∧ FormallyUnramified (U.ι ≫ projection f)) (k : ℕ)
    (h : ∀ n, Dense ((rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t) ⁻¹' Set.range c)) :
    RingHom.ker (c).appTop.hom ≤ RingHom.ker t.appTop.hom :=
  originalBoundary_kernel_zero_of_local_image_coverage e J hJ t hU
    (originalBoundary_coverage_of_dense_rankStages J hJ t k h)

end FLT.Mazur.EquivalenceRelationOrderedFrames

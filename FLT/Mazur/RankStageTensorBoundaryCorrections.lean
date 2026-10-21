/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryTensorLift
public import FLT.Mazur.RankStageCoreCorrectionSpace

/-!
# One descended scalar for every whole-core rank correction

An actual full flat tensor boundary solution constructs an original multiplier
before the rank and atlas are chosen. The proved forward original-lift bridge
then solves the entire boundary and every mixed equation at every rank.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
open RingPairInvariantFlatScalars FlatAlgebraEqualizer
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance tensorBoundaryOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance tensorBoundaryOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance tensorBoundaryOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local irreducible] rankStageCoreCorrectionIdeal
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
variable (J : A.IdealSheafData) (t : Γ(J.subscheme, ⊤))
  (S : Type) [CommRing S] [Algebra (invariants p.appTop.hom q.appTop.hom) S]
  [Module.Flat (invariants p.appTop.hom q.appTop.hom) S]
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "α" => first p.appTop.hom q.appTop.hom
local notation "β" => second p.appTop.hom q.appTop.hom

/-- One original scalar away from the branch prime works for every whole-core rank atlas. -/
theorem exists_uniform_rankStage_multiplier_of_tensor
    (P : Ideal S) (s : S) (hs : s ∉ P) (a : S ⊗[R] Γ(A, ⊤))
    (he : tensorMap S α a = tensorMap S β a)
    (hb : tensorMap S (originalBoundaryMap J) a =
      algebraMap S (S ⊗[R] Γ(J.subscheme, ⊤)) s * (1 ⊗ₜ[R] t)) :
    ∃ r : compatibleFunctions p q, algebraMap R S r ∉ P ∧
      ∀ (n : ℕ) (ι : Type) (c : ι → Γ(A, ⊤))
        (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
        (v : ∀ j, rankStageCompatibleCoreInvariants e n (c j) (hc j)),
        (∀ j l, (rankStageCoreBoundaryIdeal e n (c j) (hc j) J l).subschemeι.appTop
          ((v j).val l).val =
            (rankStageCoreOriginalBoundaryMap e n (c j) (hc j) J l).appTop t) →
        r ∈ rankStageCoreCorrectionIdeal e n c hc J v := by
  obtain ⟨r, hr, hrt⟩ :=
    exists_originalBoundaryLift_multiplier_of_tensor J S P t s hs a he hb
  refine ⟨r, hr, fun n _ c hc v hv ↦ ?_⟩
  exact originalBoundaryLiftIdeal_le_correctionIdeal J t e n c hc v hv hrt

end FLT.Mazur.EquivalenceRelationOrderedFrames

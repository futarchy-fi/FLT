/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryFrameScalarNorm
public import FLT.Mazur.RelationOriginalEndpointCoordinate
public import FLT.Mazur.RelativeFrameCoordinateSeparation
public import FLT.Mazur.InvariantIdealRelationMonomorphism

/-!
# Constructed original scalar coordinates of boundary frames

Each geometric frame coordinate supplies an actual original relation arrow.
Its second endpoint is compatible with all original invariant scalars.
Joint monicity and distinctness prove pairwise separation in the whole
original source coefficient ring, without a pre-existing product frame.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators
open Module TensorProduct
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "P" => pullback.snd p J.subschemeι
local notation "Q" => InvariantIdealRelation.snd J p q hJ
local notation "E" => Over.mk P
local instance separatedCoordinateBoundaryOver_separated : IsSeparated (E).hom :=
  inferInstanceAs (IsSeparated P)
local instance separatedCoordinateOriginalOver_separated : IsSeparated (Over.mk p).hom :=
  ‹IsSeparated p›
variable (x : B ⟶ J.subscheme) (n : ℕ)
  (a : Over.mk x ⟶ distinctScheme (Over.mk (pullback.snd p J.subschemeι)) (Fin n))

local notation "s" k:max => testSection E (Fin n) a k

local notation "l" k:max => (s k ≫ pullback.fst P x ≫ Q).appTop.hom


/-- The original relation arrow underlying a boundary frame coordinate. -/
def originalBoundaryFrameSourceArrow (k : Fin n) : B ⟶ D :=
  s k ≫ pullback.fst P x ≫ pullback.fst p J.subschemeι

/-- Every constructed source arrow retains the actual original first endpoint. -/
@[reassoc] theorem originalBoundaryFrameSourceArrow_first (k : Fin n) :
    originalBoundaryFrameSourceArrow J x n a k ≫ p = x ≫ J.subschemeι := by
  dsimp only [originalBoundaryFrameSourceArrow]
  rw [Category.assoc, Category.assoc, pullback.condition, pullback.condition_assoc]
  simpa only [Over.mk_hom, Category.id_comp] using
    testSection_snd_assoc E (Fin n) a k (x ≫ J.subschemeι)

/-- The source arrow retains the actual boundary second endpoint in the uncut source. -/
@[reassoc] theorem originalBoundaryFrameSourceArrow_second (k : Fin n) :
    originalBoundaryFrameSourceArrow J x n a k ≫ q =
      (s k ≫ pullback.fst P x ≫ Q) ≫ J.subschemeι := by
  simp only [originalBoundaryFrameSourceArrow, Category.assoc, InvariantIdealRelation.snd_ι]

variable [Algebra (invariants p.appTop.hom q.appTop.hom) Γ(B, ⊤)]
  (hscalar : algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(B, ⊤) =
    x.appTop.hom.comp
      (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))

/-- The frame supplies scalar-compatible maps from the whole uncut original source. -/
def originalBoundaryFrameSourceCoordinate (k : Fin n) : Γ(A, ⊤) →ₐ[R] Γ(B, ⊤) :=
  RelationOriginalScalarCoordinate.coordinate p q (x ≫ J.subschemeι) hscalar
    (originalBoundaryFrameSourceArrow J x n a k)
    (originalBoundaryFrameSourceArrow_first J x n a k)

variable [IsAffine A] [IsAffine B] (e : CategoryTheory.EquivalenceRelation p q)
include e

/-- Distinct geometric coordinates separate the full original source coefficients. -/
theorem originalBoundaryFrameSourceCoordinate_separated :
    Pairwise fun i j ↦ FiniteCoefficientDifference.differenceIdeal
      (originalBoundaryFrameSourceCoordinate (p := p) (q := q) J x n a hscalar i).toRingHom
      (originalBoundaryFrameSourceCoordinate (p := p) (q := q) J x n a hscalar j).toRingHom =
        ⊤ := by
  let _ : JointlyMono₂ p q := e.toJointlyMono₂
  let _ : JointlyMono₂ (E).hom (pullback.fst p J.subschemeι ≫ q) := ⟨by
    intro T u v hp hq
    apply pullback.hom_ext
    · apply JointlyMono₂.right_cancellation (p₁ := p) (p₂ := q)
      · simpa only [Category.assoc, pullback.condition, Over.mk_hom] using
          congrArg (fun g ↦ g ≫ J.subschemeι) hp
      · simpa only [Category.assoc] using hq
    · exact hp⟩
  intro i j hij
  change FiniteCoefficientDifference.differenceIdeal
    (originalBoundaryFrameSourceArrow J x n a i ≫ q).appTop.hom
    (originalBoundaryFrameSourceArrow J x n a j ≫ q).appTop.hom = ⊤
  simpa only [originalBoundaryFrameSourceArrow, Category.assoc, Over.mk_hom] using
    frameCoordinate_differenceIdeal_eq_top E (Fin n) a
      (pullback.fst p J.subschemeι ≫ q) i j hij

end FLT.Mazur.EquivalenceRelationOrderedFrames

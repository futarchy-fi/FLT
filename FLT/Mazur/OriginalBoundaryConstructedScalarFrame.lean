/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryFrameScalarNorm
public import FLT.Mazur.OriginalBoundaryAmbientFiniteFreeLift
public import FLT.Mazur.OriginalBoundarySeparatedSourceCoordinates
public import FLT.Mazur.FiniteFreeSeparatedScalarFrame

/-!
# Full boundary lifts from constructed geometric scalar frames

A genuine whole-source basis of the frame's rank is the sole remaining
algebraic input. The coordinate maps, original separation, complete scalar
frame, and original boundary comparison arrow are all constructed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators
open Module TensorProduct
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem composite_coefficient {X Y Z : Scheme.{0}}
    (u : X ⟶ Z) (v : X ⟶ Y) (w : Y ⟶ Z) (h : u = v ≫ w) (z : Γ(Z, ⊤)) :
    u.appTop z = v.appTop (w.appTop z) :=
  congrArg (fun g : X ⟶ Z ↦ g.appTop z) h

variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "P" => pullback.snd p J.subschemeι
local notation "Q" => InvariantIdealRelation.snd J p q hJ
local notation "E" => Over.mk P
local notation "c" => originalBoundaryComparison p q J hJ
local instance constructedFrameBoundaryOver_separated : IsSeparated (E).hom :=
  inferInstanceAs (IsSeparated P)
local instance constructedFrameBoundaryOver_etale : Etale (E).hom := inferInstanceAs (Etale P)
local instance constructedFrameBoundaryOver_compact : QuasiCompact (E).hom :=
  inferInstanceAs (QuasiCompact P)
local instance constructedFrameOriginalOver_separated : IsSeparated (Over.mk p).hom :=
  ‹IsSeparated p›
local instance constructedFrameOriginalOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance constructedFrameOriginalOver_compact : QuasiCompact (Over.mk p).hom :=
  ‹QuasiCompact p›
variable (t : B ⟶ pullback
    (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))
    (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤))))
  (n : ℕ)
local notation "x" => t ≫ pullback.fst f f
local notation "y" => t ≫ pullback.snd f f
variable (a : Over.mk (t ≫ pullback.fst _ _) ⟶
    distinctScheme (Over.mk (pullback.snd p J.subschemeι)) (Fin n))
  (ht : Set.range (t ≫ pullback.fst _ _ ≫ J.subschemeι) ⊆ exactRank (Over.mk p) n)

variable [IsAffine A] [IsAffine B] [LocallyQuasiFinite p]
  (e : CategoryTheory.EquivalenceRelation p q)
local instance constructedFrameBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
local instance constructedFrameOriginal_quasiFinite : LocallyQuasiFinite (Over.mk p).hom :=
  ‹LocallyQuasiFinite p›
attribute [local irreducible] scalarMorphism
local notation "s" k:max => testSection E (Fin n) a k

local notation "l" k:max => (s k ≫ pullback.fst P x ≫ Q).appTop.hom
local notation "r" => (y).appTop.hom

local notation "σ" => algebraMap R Γ(J.subscheme, ⊤)

variable [Algebra (invariants p.appTop.hom q.appTop.hom) Γ(B, ⊤)]
  (hscalar : algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(B, ⊤) =
    (t ≫ pullback.fst _ _).appTop.hom.comp
      (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))


/-- Geometric coordinates and a matching whole-source basis construct the full scalar frame. -/
def originalBoundaryConstructedScalarFrame (basis : Basis (Fin n) R Γ(A, ⊤)) :
    (Γ(B, ⊤) ⊗[R] Γ(A, ⊤)) ≃ₐ[Γ(B, ⊤)] (Fin n → Γ(B, ⊤)) :=
  FiniteFreeSeparatedScalarFrame.frame basis
    (originalBoundaryFrameSourceCoordinate (p := p) (q := q) J x n a hscalar)
    (originalBoundaryFrameSourceCoordinate_separated J x n a hscalar e)

omit [Etale p] [QuasiCompact p] [LocallyQuasiFinite p] in
/-- The constructed frame evaluates uncut coefficients on actual original relation arrows. -/
theorem originalBoundaryConstructedScalarFrame_coefficient
    (basis : Basis (Fin n) R Γ(A, ⊤)) (k : Fin n) (z : Γ(A, ⊤)) :
    originalBoundaryConstructedScalarFrame J t n a e hscalar basis (1 ⊗ₜ[R] z) k =
      (originalBoundaryFrameSourceArrow J x n a k ≫ q).appTop z :=
  FiniteFreeSeparatedScalarFrame.frame_coefficient basis
    (originalBoundaryFrameSourceCoordinate (p := p) (q := q) J x n a hscalar)
    (originalBoundaryFrameSourceCoordinate_separated J x n a hscalar e) z k


include ht a e hscalar in
/-- A matching uncut source basis now constructs the unique full original boundary arrow. -/
theorem originalBoundary_frame_lift_of_matching_source_basis
    (basis : Basis (Fin n) R Γ(A, ⊤)) :
    ∃! u : B ⟶ pullback p J.subschemeι, u ≫ c = t := by
  exact originalBoundary_frame_lift_of_ambient_finiteFree_source J hJ t n a ht e hscalar
    basis (originalBoundaryConstructedScalarFrame J t n a e hscalar basis)
    (fun k z ↦ by
      rw [originalBoundaryConstructedScalarFrame_coefficient]
      exact composite_coefficient _ _ _
        (originalBoundaryFrameSourceArrow_second J hJ x n a k) z)

end FLT.Mazur.EquivalenceRelationOrderedFrames

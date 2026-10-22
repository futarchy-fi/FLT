/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryFramePolynomial
public import FLT.Mazur.ScalarPolynomialNormEquation
public import FLT.Mazur.SchemeScalarKernelPairSymmetry

/-!
# Original boundary arrows from a split norm over original scalars

The constructed finite coefficient polynomial reduces the full original lift
to a scalar polynomial norm with a full-frame splitting and its source root
identity. Scalar agreement is proved from the actual kernel pair; no full
invariant-ring surjectivity, reduced test, or power cancellation is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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
local instance normPolynomialBoundaryOver_separated : IsSeparated (E).hom :=
  inferInstanceAs (IsSeparated P)
local instance normPolynomialBoundaryOver_etale : Etale (E).hom := inferInstanceAs (Etale P)
local instance normPolynomialBoundaryOver_compact : QuasiCompact (E).hom :=
  inferInstanceAs (QuasiCompact P)
local instance normPolynomialOriginalOver_separated : IsSeparated (Over.mk p).hom :=
  ‹IsSeparated p›
local instance normPolynomialOriginalOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance normPolynomialOriginalOver_compact : QuasiCompact (Over.mk p).hom :=
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
local instance normPolynomialBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
local instance normPolynomialOriginal_quasiFinite : LocallyQuasiFinite (Over.mk p).hom :=
  ‹LocallyQuasiFinite p›
attribute [local irreducible] scalarMorphism
local notation "s" k:max => testSection E (Fin n) a k

local notation "l" k:max => (s k ≫ pullback.fst P x ≫ Q).appTop.hom
local notation "r" => (y).appTop.hom

local notation "σ" => algebraMap R Γ(J.subscheme, ⊤)

omit [IsSeparated p] [Etale p] [QuasiCompact p] [IsAffine A] [IsAffine B]
  [LocallyQuasiFinite p] in
/-- Both actual endpoints agree on every unchanged original scalar on the whole test. -/
theorem originalBoundary_frame_scalar_maps_eq :
    (x).appTop.hom.comp σ = (y).appTop.hom.comp σ := by
  ext z
  change t.appTop ((pullback.fst f f).appTop (σ z)) =
    t.appTop ((pullback.snd f f).appTop (σ z))
  exact congrArg t.appTop (scalarKernelPair_endpoints σ z)

variable [IsNoetherianRing Γ(B, ⊤)]
local notation "G" => originalBoundaryFramePolynomial J hJ t n a
include ht e

/-- A split original scalar norm constructs the unique full boundary comparison arrow. -/
theorem originalBoundary_frame_lift_of_scalar_norm
    (N : Polynomial (Polynomial R))
    (hroot : (N.map (Polynomial.mapRingHom σ)).eval G = 0)
    (hsplit : N.map (Polynomial.mapRingHom ((x).appTop.hom.comp σ)) =
      ∏ k : Fin n, (Polynomial.C ((G).map (l k)) - Polynomial.X)) :
    ∃! d : B ⟶ pullback p J.subschemeι, d ≫ c = t := by
  apply (originalBoundary_frame_lift_iff_polynomial J hJ t n a ht e).mpr
  exact ScalarPolynomialNormEquation.differenceProduct_eq_zero σ (x).appTop.hom r
    (fun k ↦ l k) (originalBoundary_frame_scalar_maps_eq J t) G N hroot hsplit

end FLT.Mazur.EquivalenceRelationOrderedFrames

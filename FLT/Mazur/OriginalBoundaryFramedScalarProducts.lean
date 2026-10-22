/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryFramedEquationIdeal
public import FLT.Mazur.RelativeFrameEquationProducts

/-!
# Exact original boundary comparison products

The original exact rank constructs full-source finiteness. The equivalence
relation then makes its comparison a closed immersion. Consequently, on an
affine framed coefficient test, the original comparison ideal is exactly the
product of the coordinate coefficient difference ideals.
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
local instance productEquationBoundaryOver_separated : IsSeparated (E).hom :=
  inferInstanceAs (IsSeparated P)
local instance productEquationBoundaryOver_etale : Etale (E).hom := inferInstanceAs (Etale P)
local instance productEquationBoundaryOver_compact : QuasiCompact (E).hom :=
  inferInstanceAs (QuasiCompact P)
local instance productEquationOriginalOver_separated : IsSeparated (Over.mk p).hom :=
  ‹IsSeparated p›
local instance productEquationOriginalOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance productEquationOriginalOver_compact : QuasiCompact (Over.mk p).hom :=
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
local instance productEquationBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
local instance productEquationOriginal_quasiFinite : LocallyQuasiFinite (Over.mk p).hom :=
  ‹LocallyQuasiFinite p›
attribute [local irreducible] scalarMorphism
local notation "u" => pullback.fst P x ≫ Q
local notation "w" => pullback.snd P x ≫ y
local notation "v" => equalizer.ι u w ≫ pullback.snd P x
local notation "i" => RelationComparisonEquation.iso P Q f c
  (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) t
include ht e

omit [IsAffine B] in
/-- Rank finiteness and the original relation close the full framed endpoint equation. -/
theorem originalBoundary_frameEquation_closedImmersion : IsClosedImmersion v := by
  let _ : IsFinite (pullback.snd p (t ≫ pullback.fst f f ≫ J.subschemeι)) :=
    finite_pullback_of_exactRank (Over.mk p) n _ ht
  let _ := originalBoundary_comparison_test_closedImmersion J hJ t e
  have hi : (i).inv ≫ pullback.snd c t = v :=
    RelationComparisonEquation.fromEquation_snd P Q f c
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) t
  rw [← hi]
  infer_instance

/-- Exact original coordinate scalar ideals, before taking products or radicals. -/
abbrev originalBoundaryFrameScalarIdeal (k : Fin n) : Ideal Γ(B, ⊤) :=
  frameEquationScalarIdeal E (Fin n) a Q y k

/-- The exact scalar kernel of the actual original comparison is a product of differences. -/
theorem originalBoundary_frame_scalar_kernel_product :
    RingHom.ker (pullback.snd c t).appTop.hom =
      ∏ k : Fin n, originalBoundaryFrameScalarIdeal J hJ t n a k := by
  let _ := originalBoundary_frameEquation_closedImmersion J hJ t n ht e
  have he : (pullback.snd c t).ker = (v).ker := by
    rw [← RelationComparisonEquation.iso_projection P Q f c
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) t,
      Scheme.Hom.ker_comp_of_isIso]
  have hs : RingHom.ker (pullback.snd c t).appTop.hom = RingHom.ker (v).appTop.hom := by
    apply Scheme.IdealSheafData.equivOfIsAffine.symm.injective
    change Scheme.IdealSheafData.ofIdealTop _ = Scheme.IdealSheafData.ofIdealTop _
    simpa only [← Scheme.ker_of_isAffine] using he
  rw [hs]
  exact frameEquation_scalar_kernel_product E (Fin n) a Q y
    (IsClosedImmersion.isClosedEmbedding v).injective
    (originalBoundary_frame_complete J t n a ht)

end FLT.Mazur.EquivalenceRelationOrderedFrames

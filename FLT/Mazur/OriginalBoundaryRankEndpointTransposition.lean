/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryRankTransposition

/-!
# Full boundary endpoint equations under rank transposition

Transposition exchanges the two full boundary restrictions and negates their
additive discrepancy. This transports actual section equations, not merely
scalar support. In particular it does not assert equality of the endpoints.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem section_of_composition {X Y Z : Scheme.{0}}
    (i : X ⟶ Y) (a : Y ⟶ Z) (b : X ⟶ Z) (h : i ≫ a = b) (t : Γ(Z, ⊤)) :
    i.appTop (a.appTop t) = b.appTop t :=
  congrArg (fun g : X ⟶ Z ↦ g.appTop t) h

private theorem map_sub_eq_neg_sub {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (a b : R) (c d : S) (ha : f a = d) (hb : f b = c) :
    f (a - b) = -(c - d) := by
  rw [map_sub, ha, hb, neg_sub]

variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (J : A.IdealSheafData)
local instance transposeEndpointOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance transposeEndpointOver_etale : Etale (Over.mk p).hom := ‹Etale p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
attribute [local irreducible] doubleRankMap doubleRankThickening
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "τ" => (pullbackSymmetry f f).hom
variable (n m r s : ℕ)
local notation "l" => doubleRankMap (Over.mk p) x y n m r s
local notation "l'" => doubleRankMap (Over.mk p) x y m n s r
local notation "ι" => (originalBoundaryDoubleRankTransposeIso (p := p) (q := q) J n m r s).hom

/-- The complete original first endpoint becomes the second endpoint after transposition. -/
@[reassoc (attr := simp)]
theorem originalBoundary_rank_transpose_first :
    ι ≫ l' ≫ pullback.fst f f = l ≫ pullback.snd f f := by
  have h : ι ≫ l' = l ≫ τ := doubleRankTranspose_map (Over.mk p) x y τ
    (pullbackSymmetry_hom_comp_fst_assoc _ _ _) (pullbackSymmetry_hom_comp_snd_assoc _ _ _)
    n m r s
  rw [← Category.assoc, h, Category.assoc, pullbackSymmetry_hom_comp_fst]

/-- The complete original second endpoint becomes the first endpoint after transposition. -/
@[reassoc (attr := simp)]
theorem originalBoundary_rank_transpose_second :
    ι ≫ l' ≫ pullback.snd f f = l ≫ pullback.fst f f := by
  have h : ι ≫ l' = l ≫ τ := doubleRankTranspose_map (Over.mk p) x y τ
    (pullbackSymmetry_hom_comp_fst_assoc _ _ _) (pullbackSymmetry_hom_comp_snd_assoc _ _ _)
    n m r s
  rw [← Category.assoc, h, Category.assoc, pullbackSymmetry_hom_comp_snd]

/-- Every full boundary section follows the exchanged first endpoint. -/
theorem originalBoundary_rank_transpose_first_section (t : Γ(J.subscheme, ⊤)) :
    (ι).appTop ((l' ≫ pullback.fst f f).appTop t) = (l ≫ pullback.snd f f).appTop t := by
  exact section_of_composition _ _ _ (originalBoundary_rank_transpose_first J n m r s) t

/-- Every full boundary section follows the exchanged second endpoint. -/
theorem originalBoundary_rank_transpose_second_section (t : Γ(J.subscheme, ⊤)) :
    (ι).appTop ((l' ≫ pullback.snd f f).appTop t) = (l ≫ pullback.fst f f).appTop t := by
  exact section_of_composition _ _ _ (originalBoundary_rank_transpose_second J n m r s) t

/-- Transposition negates the full two-endpoint discrepancy, retaining all nilpotents. -/
theorem originalBoundary_rank_discrepancy_transpose (t : Γ(J.subscheme, ⊤)) :
    (ι).appTop ((l' ≫ pullback.fst f f).appTop t - (l' ≫ pullback.snd f f).appTop t) =
      -((l ≫ pullback.fst f f).appTop t - (l ≫ pullback.snd f f).appTop t) := by
  exact map_sub_eq_neg_sub _ _ _ _ _
    (originalBoundary_rank_transpose_first_section J n m r s t)
    (originalBoundary_rank_transpose_second_section J n m r s t)

end FLT.Mazur.EquivalenceRelationOrderedFrames

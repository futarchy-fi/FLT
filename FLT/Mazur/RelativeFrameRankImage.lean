/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameRankOpen

/-!
# Exact finite rank of original frame images

At every original base point the nonempty distinct-frame fibers form a finite
initial segment. Geometric tests prove this for the full original fiber;
the original point need not have an algebraically closed residue field.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]

/-- The actual open image of the original distinct n-frame scheme. -/
def rankImageOpen (n : ℕ) : S.Opens :=
  ⟨Set.range (distinctScheme E (Fin n)).hom,
    (distinctScheme E (Fin n)).hom.isOpenMap.isOpen_range⟩

/-- The original open with n distinct arrows and no approaching larger frame. -/
def rankStratumOpen (n : ℕ) : S.Opens := rankImageOpen E n ⊓ rankBoundOpen E n

/-- Complete geometric enumeration computes membership in every original frame image. -/
theorem geometric_mem_rankImage_iff {K : Type} [Field K] [IsSepClosed K]
    {b : Spec (.of K) ⟶ S} {n : ℕ} (a : Over.mk b ⟶ distinctScheme E (Fin n))
    (ha : Function.Bijective (fun i ↦ geometricCoordinate E (Fin n) a i default)) (m : ℕ) :
    b default ∈ rankImageOpen E m ↔ m ≤ n := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨t, ht, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
      (distinctScheme E (Fin m)).hom b y hy
    let t' : Over.mk b ⟶ distinctScheme E (Fin m) := Over.homMk t ht
    simpa only [Fintype.card_fin] using cardinality_le_complete_frame E a ha t'
  · intro hmn
    let t := a ≫ subframe E (Fin.castLEEmb hmn)
    refine ⟨t.left (default : Spec (.of K)), ?_⟩
    exact congrArg (fun f ↦ f (default : Spec (.of K))) t.w

variable [QuasiCompact E.hom]

/-- At every original point the full-frame images have an actual finite maximum rank. -/
theorem exists_point_rank (x : S) :
    ∃ n : ℕ, ∀ m : ℕ, x ∈ rankImageOpen E m ↔ m ≤ n := by
  let K := AlgebraicClosure (S.residueField x)
  let g := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x) K))
  let b := g ≫ S.fromSpecResidueField x
  have hb : b default = x := Scheme.fromSpecResidueField_apply x _
  obtain ⟨n, a, ha⟩ := exists_complete_geometric_tuple E b
  refine ⟨n, fun m ↦ ?_⟩
  rw [← hb]
  exact geometric_mem_rankImage_iff E a ha m

end FLT.Mazur.RelativeOrderedTuples

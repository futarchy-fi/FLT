/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudStageResidueRoot
public import Mathlib.FieldTheory.IsSepClosed

/-!
# The residue field of the unramified union is separably closed

Lift the coefficients of a residue polynomial to the union, descend them to
one finite stage, and adjoin a root there. All residue maps are induced by the
actual inclusions into the same union.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

namespace RaynaudParameters

variable {R Ω : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] [FaithfulSMul R Ω]
  {π : R}

/-- The actual directed union has separably closed residue field. -/
theorem unramifiedUnion_residue_isSepClosed (hπ : Irreducible π) :
    let _ := unramifiedUnion_dvr (Ω := Ω) hπ
    IsSepClosed (ResidueField (unramifiedUnion (Ω := Ω) π)) := by
  let := unramifiedUnion_dvr (Ω := Ω) hπ
  let := UnramifiedStage.nonempty (Ω := Ω) hπ
  let U := unramifiedUnion (Ω := Ω) π
  apply IsSepClosed.of_exists_root
  intro p hm hi hs
  obtain ⟨P, hPm, hP, -⟩ := exists_monic_map_residue_eq hm
  obtain ⟨S, g, _, hg, -⟩ := exists_stage_polynomial
    (fun S : UnramifiedStage (Ω := Ω) π ↦ S.1) UnramifiedStage.directed P (0 : U)
  let iS : S.1 →ₐ[R] U := Subalgebra.inclusion (le_iSup _ S)
  let : IsLocalHom iS := unramifiedUnion_local_inclusion hπ S
  let : IsLocalHom iS.toRingHom := ⟨fun x hx ↦ isUnit_of_map_unit iS x hx⟩
  change g.map iS.toRingHom = P at hg
  let φS := ResidueField.map iS.toRingHom
  let q := g.map (residue S.1)
  have hq : q.map φS = p := by
    change (g.map (residue S.1)).map (ResidueField.map iS.toRingHom) = p
    rw [Polynomial.map_map, ResidueField.map_comp_residue, ← Polynomial.map_map, hg, hP]
  have hqm : q.Monic := Polynomial.monic_of_injective φS.injective (hq ▸ hm)
  have hqs : q.Separable := (Polynomial.separable_map φS).mp (hq ▸ hs)
  have hqd : q.degree ≠ 0 := by
    rw [← degree_map_eq_of_injective φS.injective, hq]
    exact (degree_pos_of_irreducible hi).ne'
  obtain ⟨T, hST, y, hy⟩ := exists_larger_stage_residue_root S q hqm hqs hqd
  let iT : T.1 →ₐ[R] U := Subalgebra.inclusion (le_iSup _ T)
  let : IsLocalHom iT := unramifiedUnion_local_inclusion hπ T
  let : IsLocalHom iT.toRingHom := ⟨fun x hx ↦ isUnit_of_map_unit iT x hx⟩
  let φT := ResidueField.map iT.toRingHom
  have hcomp : φT.comp (ResidueField.map (Subalgebra.inclusion hST).toRingHom) = φS := by
    ext a
    obtain ⟨a, rfl⟩ := residue_surjective a
    rfl
  refine ⟨φT (residue T.1 y), ?_⟩
  rw [← hq, Polynomial.eval_map, ← hcomp, ← Polynomial.hom_eval₂, hy, map_zero]

end RaynaudParameters

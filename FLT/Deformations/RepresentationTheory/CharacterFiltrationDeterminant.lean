/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.ReducibleFiltration
public import FLT.Deformations.RepresentationTheory.TrivialQuotientKernel

/-! # Determinant of an actual character filtration

The two character values multiply to the determinant even when the extension
is nonsplit. The proof uses the invariant kernel and its actual quotient.
-/

@[expose] public noncomputable section
namespace GaloisRep.CharacterFiltration
variable {K k V : Type*} [Field K] [Field k] [TopologicalSpace k]
  [DiscreteTopology k] [AddCommGroup V] [Module k V] [Module.Finite k V]
  {ρ : GaloisRep K k V} (F : CharacterFiltration ρ)

omit [DiscreteTopology k] in
/-- Character values on a line act by scalar multiplication. -/
theorem line_apply (χ : GaloisRep K k k) (g : Field.absoluteGaloisGroup K) (a : k) :
    χ g a = χ g 1 * a := by
  calc
    χ g a = a • χ g 1 := by simpa using (χ g).map_smul a (1 : k)
    _ = χ g 1 * a := mul_comm _ _

omit [DiscreteTopology k] in
/-- On a rank-two exact character filtration, the determinant is the product. -/
theorem det_eq_product (hdim : Module.finrank k V = 2) (g : Field.absoluteGaloisGroup K) :
    (ρ g).det = F.χ₁ g 1 * F.χ₂ g 1 := by
  let W := LinearMap.ker F.q
  have hW : W ≤ W.comap (ρ g) := by
    intro x hx
    change F.q (ρ g x) = 0
    rw [F.q_equivariant, show F.q x = 0 from hx, map_zero]
  have hdW : Module.finrank k W = 1 :=
    LinearMap.finrank_ker_of_rank_two F.q F.q_surjective hdim
  have hdQ : Module.finrank k (V ⧸ W) = 1 := by
    have h := W.finrank_quotient_add_finrank
    rw [hdW, hdim] at h
    omega
  have hrest : (ρ g).restrict (p := W) (q := W) (fun _ hx ↦ hW hx) = (F.χ₁ g 1) • LinearMap.id := by
    ext x
    have hx : x.val ∈ LinearMap.range F.i := by
      rw [F.exactness]
      exact x.property
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hx
    change ρ g x.val = (F.χ₁ g 1) • x.val
    rw [← ha, F.i_equivariant, line_apply]
    exact F.i.map_smul (F.χ₁ g 1) a
  have hquot : W.mapQ W (ρ g) hW = (F.χ₂ g 1) • LinearMap.id := by
    ext x
    change W.mkQ (ρ g x) = (F.χ₂ g 1) • W.mkQ x
    rw [← map_smul]
    apply (Submodule.Quotient.eq W).mpr
    change F.q (ρ g x - (F.χ₂ g 1) • x) = 0
    rw [map_sub, map_smul, F.q_equivariant, line_apply]
    exact sub_self _
  rw [LinearMap.det_eq_det_mul_det W _ hW, hrest, hquot]
  simp only [LinearMap.det_smul, hdW, hdQ, pow_one, LinearMap.det_id, mul_one]

end GaloisRep.CharacterFiltration

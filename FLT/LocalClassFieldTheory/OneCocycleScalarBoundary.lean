/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.OneCocycleExtension
public import FLT.LocalClassFieldTheory.ScalarCochainCup

/-!
# The first boundary is cup with a one-cocycle

The canonical lift of a scalar cocycle has differential equal to its cup with
the extension cocycle. This computes the genuine connecting map in every degree.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G] (Q : Rep.{0} k G) (b : cocycles₁ Q)
  {n : ℕ} (z : (Fin n → G) → k)
  (hz : inhomogeneousCochains.d (Rep.trivial k G k) n z = 0)

include hz

/-- The differential of the canonical scalar lift is the cup with the extension cocycle. -/
theorem oneCocycle_scalarLift_d :
    (oneCocycleInclusion Q b).hom ∘ scalarCupOne Q b z =
      (inhomogeneousCochains (oneCocycleExtension Q b)).d n (n + 1)
        (fun v => (0, z v)) := by
  funext v
  rw [inhomogeneousCochains.d_def, inhomogeneousCochains.d_hom_apply]
  apply Prod.ext
  · change z (fun i => v i.succ) • b (v 0) =
      (Q.ρ (v 0) 0 + z (fun i => v i.succ) • b (v 0)) +
        (∑ j : Fin (n + 1), (-1 : k) ^ (j.val + 1) •
          ((0, z (Fin.contractNth j (· * ·) v)) : Q × k)).1
    rw [show (∑ j : Fin (n + 1), (-1 : k) ^ (j.val + 1) •
      ((0, z (Fin.contractNth j (· * ·) v)) : Q × k)).1 = 0 from by
        change (LinearMap.fst k Q k) _ = 0
        simp]
    simp
  · have hv : inhomogeneousCochains.d (Rep.trivial k G k) n z v = 0 := congrFun hz v
    change 0 = z (fun i => v i.succ) + (LinearMap.snd k Q k)
      (∑ j : Fin (n + 1), (-1 : k) ^ (j.val + 1) •
        ((0, z (Fin.contractNth j (· * ·) v)) : Q × k))
    simpa [inhomogeneousCochains.d_hom_apply, Pi.zero_apply] using hv.symm

/-- The explicit first cup is a cocycle, proved in the actual coefficient sequence. -/
theorem scalarCupOne_cycle : inhomogeneousCochains.d Q (n + 1) (scalarCupOne Q b z) = 0 := by
  have hS := map_cochainsFunctor_shortExact (oneCocycleSequence_shortExact Q b)
  have h := hS.d_eq_zero_of_f_eq_d_apply n (n + 1) (fun v => (0, z v))
      (scalarCupOne Q b z) (by
        exact oneCocycle_scalarLift_d Q b z hz) (n + 2)
  change (inhomogeneousCochains Q).d (n + 1) (n + 2) (scalarCupOne Q b z) = 0 at h
  rw [inhomogeneousCochains.d_def] at h
  exact h

/-- Every ordinary connecting map of this extension is the explicit cochain cup. -/
theorem oneCocycle_connecting_scalarCup :
    groupCohomology.δ (oneCocycleSequence_shortExact Q b) n (n + 1) rfl
      (π (Rep.trivial k G k) n (cocyclesMk z hz)) =
        π Q (n + 1) (cocyclesMk (scalarCupOne Q b z) (scalarCupOne_cycle Q b z hz)) := by
  exact δ_apply (oneCocycleSequence_shortExact Q b) rfl z
    (by simpa [oneCocycleSequence, CochainComplex.of.d] using hz)
    (fun v => (0, z v)) rfl (scalarCupOne Q b z)
      (oneCocycle_scalarLift_d Q b z hz)

end LocalClassFieldTheory

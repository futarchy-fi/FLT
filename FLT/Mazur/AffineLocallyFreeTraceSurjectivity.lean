/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTracePrincipalPower

/-!
# Surjectivity of the full finite locally free étale trace

Principal refinements of the given finite free cover supply powers in the
global trace range. Their basic opens cover the original affine target, so
the range is the unit ideal. No global basis or constant rank is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineLocallyFreeTraceSurjectivity
universe u v
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
  (f : X ⟶ Y) (r : Y ⟶ X) (hr : r ≫ f = 𝟙 Y) [Etale f]
  {ι : Type v} (U : ι → Y.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis f (U i)) (hcover : ⨆ i, (U i).1 = ⊤)

include hr in
/-- Actual locally free chart traces generate the unit ideal over the original target. -/
theorem range_eq_top :
    let _ := f.appTop.hom.toAlgebra
    LinearMap.range (AffineTraceGluing.linearMap f U hU hcover) = ⊤ := by
  let _ := f.appTop.hom.toAlgebra
  let I : Ideal Γ(Y, ⊤) := LinearMap.range (AffineTraceGluing.linearMap f U hU hcover)
  have hc : ⨆ a : (I : Set Γ(Y, ⊤)), Y.basicOpen a.val = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover.symm ▸ hx)
    obtain ⟨a, ha, hxa⟩ := (isAffineOpen_top Y).exists_basicOpen_le
      (⟨x, hi⟩ : (U i).1) (show x ∈ (⊤ : Y.Opens) from trivial)
    have hV := (hU i).restrict f
      (show (⟨Y.basicOpen a, (isAffineOpen_top Y).basicOpen a⟩ : Y.affineOpens) ≤ U i
        from ha)
    obtain ⟨n, hn⟩ := AffineTracePrincipalPower.exists_power_mem_range
      f r hr U hU hcover a hV
    have hmem : a ^ (n + 1) ∈ I := by
      rw [pow_succ']
      exact I.mul_mem_left a hn
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨⟨a ^ (n + 1), hmem⟩, ?_⟩
    simpa only [Y.basicOpen_pow a (Nat.succ_pos n)] using hxa
  exact (Ideal.span_eq I).symm.trans
    ((isAffineOpen_top Y).iSup_basicOpen_eq_self_iff.mp hc)

include hr in
/-- Every target function is the trace of a full original source function. -/
theorem trace_surjective :
    Function.Surjective (AffineTraceGluing.trace f U hU hcover) := by
  let _ := f.appTop.hom.toAlgebra
  exact LinearMap.range_eq_top.mp (range_eq_top f r hr U hU hcover)

include hr in
/-- A trace-one element exists over the original ring, with no chosen global basis. -/
theorem exists_trace_one :
    ∃ s : Γ(X, ⊤), AffineTraceGluing.trace f U hU hcover s = 1 :=
  trace_surjective f r hr U hU hcover 1

end FLT.Mazur.AffineLocallyFreeTraceSurjectivity

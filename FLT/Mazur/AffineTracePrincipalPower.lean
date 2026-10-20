/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizedTracePower
public import FLT.Mazur.AffineTraceLinearMap
public import FLT.Mazur.AffineEtaleTraceCharts

/-!
# Principal-open trace units in the original global range

Actual section localizations clear the denominator of a local trace unit.
The result is a power in the range of the unchanged glued global trace.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineTracePrincipalPower
universe u v
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
  (f : X ⟶ Y) (r : Y ⟶ X) (hr : r ≫ f = 𝟙 Y) [Etale f]
  {ι : Type v} (U : ι → Y.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis f (U i)) (hcover : ⨆ i, (U i).1 = ⊤)

include hr in
/-- Finite freeness over a principal target open puts a parameter power in the trace range. -/
theorem exists_power_mem_range (a : Γ(Y, ⊤))
    (ha : AffineOpenNorm.HasBasis f ⟨Y.basicOpen a, (isAffineOpen_top Y).basicOpen a⟩) :
    let _ := f.appTop.hom.toAlgebra
    ∃ n : ℕ, a ^ n ∈ LinearMap.range (AffineTraceGluing.linearMap f U hU hcover) := by
  let _ := f.appTop.hom.toAlgebra
  let V : Y.affineOpens := ⟨Y.basicOpen a, (isAffineOpen_top Y).basicOpen a⟩
  let C := f ⁻¹ᵁ V.1
  let _ := V.1.ι.appTop.hom.toAlgebra
  let _ := C.ι.appTop.hom.toAlgebra
  let _ : IsLocalization.Away a Γ(V.1.toScheme, ⊤) := inferInstance
  let _ : IsLocalization.Away (f.appTop a) Γ(C.toScheme, ⊤) := by
    have hC : C = X.basicOpen (f.appTop a) := Scheme.preimage_basicOpen_top f a
    exact (isAffineOpen_top X).isLocalization_of_eq_basicOpen (f.appTop a) _
      ((TopologicalSpace.Opens.isOpenEmbedding_obj_top C).trans hC)
  apply LocalizedTracePower.exists_power_mem_range a (f ∣_ V.1).appTop.hom
    (AffineTraceGluing.linearMap f U hU hcover)
    (AffineCartesianTrace.sectionTrace (f ∣_ V.1))
  · intro b
    exact congrArg (fun k : C.toScheme ⟶ Y ↦ k.appTop b)
      (morphismRestrict_ι f V.1).symm
  · intro b
    exact (AffineTraceGluing.trace_openRestrict f U hU hcover V ha b).symm
  · exact AffineCartesianTrace.sectionTrace_mul (f ∣_ V.1)
  · exact AffineEtaleTraceCharts.exists_trace_one f r hr V ha

end FLT.Mazur.AffineTracePrincipalPower

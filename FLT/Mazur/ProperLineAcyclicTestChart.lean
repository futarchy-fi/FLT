/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineFiniteFreeChart

/-!
# Positive cohomology vanishes on affine acyclic test charts

A test affine open mapping into an acyclic model chart inherits actual positive
cohomology vanishing by arbitrary affine base change. Its base need not be Noetherian.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve DirectImageBaseChange
variable {P X T S : Scheme.{0}} [IsLocallyNoetherian S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (U : S.Opens) (hU : IsAffineOpen U)
  (hV : ∀ s : S, s ∈ U → ∀ n,
    Subsingleton (ModuleH ((pullback (f.fiberι s)).obj L) (n + 1)))
  (W : T.Opens) [IsAffine W.toScheme] (hW : W ≤ g ⁻¹ᵁ U)

include h hL hV hU hW in
/-- Every affine test chart has vanishing positive cohomology of the original restricted line. -/
theorem properLineAcyclic_chart (n : ℕ) :
    Subsingleton (ModuleH (((pullback p).obj L).restrict (q ⁻¹ᵁ W).ι) (n + 1)) := by
  let _ : IsAffine U.toScheme := hU
  let _ : IsNoetherianRing Γ(U.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.toScheme⟩
  have hle : q ⁻¹ᵁ W ≤ p ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, h.w, Scheme.Hom.comp_preimage]
    exact q.preimage_mono hW
  let a := p.resLE (f ⁻¹ᵁ U) (q ⁻¹ᵁ W) hle
  let b := g.resLE U W hW
  have H : IsPullback a (q ∣_ W) (f ∣_ U) b := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
      Scheme.Hom.isPullback_resLE h hW (le_rfl : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U)
        (inf_eq_right.mpr hle).symm
  let N := (pullback (f ⁻¹ᵁ U).ι).obj L
  have hn := hL.pullback (f ⁻¹ᵁ U).ι
  have hv (t : U.toScheme) (n : ℕ) : Subsingleton
      (ModuleH ((pullback ((f ∣_ U).fiberι t)).obj N) (n + 1)) :=
    (properLine_fiber_vanishing_iff (isPullback_morphismRestrict f U).flip
      L hL t (n + 1)).mpr (hV (U.ι t) t.property n)
  let e : (pullback (q ⁻¹ᵁ W).ι).obj ((pullback p).obj L) ≅ (pullback a).obj N :=
    (pullbackComp (q ⁻¹ᵁ W).ι p).app L ≪≫
      (pullbackCongr (p.resLE_comp_ι hle).symm).app L ≪≫
        ((pullbackComp a (f ⁻¹ᵁ U).ι).app L).symm
  let d := (restrictFunctorIsoPullback (q ⁻¹ᵁ W).ι).app ((pullback p).obj L) ≪≫ e
  exact (Equiv.subsingleton_congr (moduleHIsoOfIso d (n + 1)).toEquiv).mpr
    (baseChange_vanishing_of_residue_fibers (f ∣_ U) N hn
      (residueAlgebra_vanishing_of_geometric (f ∣_ U) N hn hv) H n)

end FLT.Mazur.LineSectionBaseChange

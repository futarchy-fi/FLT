/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperGeometricRankOneOpen
public import FLT.Mazur.ProperLineRankOneOpenFactorization
public import FLT.Mazur.LocallyFiniteFreeOpenCover

/-!
# Finite free direct images on acyclic model charts

Every test open mapping into an acyclic affine chart of a Noetherian model
has a locally finite free actual direct image, without restrictions on the test.
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
  (W : T.Opens) (hW : W ≤ g ⁻¹ᵁ U)

include h hL hV hU hW in
/-- Acyclic model charts construct finite free charts on the actual test direct image. -/
theorem properLineFiniteFree_chart :
    LocallyFiniteFree ((pullback W.ι).obj ((pushforward q).obj ((pullback p).obj L))) := by
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
  let d := openIso q W ((pullback p).obj L) ≪≫ (pushforward (q ∣_ W)).mapIso e
  have hv' := residueAlgebra_vanishing_of_geometric (f ∣_ U) N hn hv
  exact ((properLinePushforward_locallyFiniteFree (f ∣_ U) N hn hv').pullback b).of_iso
    (properLineArbitraryBaseChangeIso H N hn hv' ≪≫ d.symm)

end FLT.Mazur.LineSectionBaseChange

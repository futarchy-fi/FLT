/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineGeometricFiberLocus
public import FLT.Mazur.ProperLineAcyclicLocus

/-!
# Affine coefficient fibers recover the intrinsic cohomology locus

Compare the ideal residue field used by the affine cohomology construction
with the scheme's actual residue field. Both comparisons retain the original
pulled line, so the affine open is exactly the intrinsic geometric locus.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve

/-- Changing the base by an isomorphism preserves each intrinsic fiber vanishing condition. -/
theorem properLine_fiber_baseIso_iff {X S T : Scheme.{0}} (f : X ⟶ S) [IsProper f]
    (e : S ≅ T) (L : X.Modules) (hL : LocallyFreeRankOne L) (s : S) (n : ℕ) :
    Subsingleton (ModuleH ((pullback ((f ≫ e.hom).fiberι (e.hom s))).obj L) n) ↔
      Subsingleton (ModuleH ((pullback (f.fiberι s)).obj L) n) := by
  have h : IsPullback (𝟙 X) (f ≫ e.hom) f e.inv :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have hs : e.inv (e.hom s) = s := by
    rw [← Scheme.Hom.comp_apply, e.hom_inv_id]
    rfl
  have hv := properLine_fiber_vanishing_iff h L hL (e.hom s) n
  rw [hs] at hv
  let i := (pullback ((f ≫ e.hom).fiberι (e.hom s))).mapIso ((pullbackId X).app L)
  exact (Equiv.subsingleton_congr (moduleHIsoOfIso i n).toEquiv).symm.trans hv

variable {X S : Scheme.{0}} [IsAffine S] (f : X ⟶ S) [IsProper f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)

include hL in
/-- Ideal-residue coefficients detect exactly the cohomology of the geometric residue fiber. -/
theorem residueAlgebraFiber_vanishing_iff (s : S) (n : ℕ) :
    Subsingleton (ModuleH (residueAlgebraFiberLine f L (S.isoSpec.hom s)) n) ↔
      Subsingleton (ModuleH ((pullback (f.fiberι s)).obj L) n) := by
  let z := S.isoSpec.hom s
  let b := AffineBaseChangeCoefficients.baseMap S z.asIdeal.ResidueField
  let c := Spec.map (Scheme.Spec.residueFieldIso Γ(S, ⊤) z).inv
  let F := f ≫ S.isoSpec.hom
  have hc : c ≫ b = (Spec Γ(S, ⊤)).fromSpecResidueField z ≫ S.isoSpec.inv := by
    dsimp [c, b, AffineBaseChangeCoefficients.baseMap]
    rw [← Category.assoc, Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  have hb : IsPullback (𝟙 X) F f S.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨by simp [F]⟩
  have ho := (IsPullback.of_hasPullback F ((Spec Γ(S, ⊤)).fromSpecResidueField z)).paste_horiz hb
  have hw : F.fiberι z ≫ f = F.fiberToSpecResidueField z ≫ c ≫ b := by
    rw [hc]
    simpa only [Category.comp_id, Scheme.Hom.fiberι,
      Scheme.Hom.fiberToSpecResidueField] using ho.w
  let k : F.fiber z ⟶ Limits.pullback f b :=
    Limits.pullback.lift (F.fiberι z) (F.fiberToSpecResidueField z ≫ c) hw
  have hk : IsPullback k (F.fiberToSpecResidueField z) (Limits.pullback.snd f b) c := by
    apply IsPullback.of_right (h₁₂ := Limits.pullback.fst f b)
      (h₂₂ := b) ?_ ?_ (IsPullback.of_hasPullback f b)
    · simpa only [k, Limits.pullback.lift_fst, hc, Category.comp_id,
        Scheme.Hom.fiberι, Scheme.Hom.fiberToSpecResidueField] using ho
    · simp [k]
  have hv := proper_line_cohomology_field_vanishing_iff hk
    (hL.pullback (Limits.pullback.fst f b)) n
  change Subsingleton (ModuleH _ n) ↔ Subsingleton (ModuleH _ n) at hv
  have he : k ≫ Limits.pullback.fst f b = F.fiberι z := by simp [k]
  let i := (pullbackComp k (Limits.pullback.fst f b)).app L ≪≫ (pullbackCongr he).app L
  exact hv.symm.trans ((Equiv.subsingleton_congr (moduleHIsoOfIso i n).toEquiv).trans
    (properLine_fiber_baseIso_iff f S.isoSpec L hL s n))

/-- The affine coefficient construction is the actual geometric cohomology locus. -/
theorem properLineAcyclicOpen_coe [IsNoetherianRing Γ(S, ⊤)] [Flat f] :
    (properLineAcyclicOpen f L hL : Set S) = properLineGeometricAcyclicLocus f L := by
  ext s
  exact forall_congr' fun n ↦ residueAlgebraFiber_vanishing_iff f L hL s (n + 1)

end FLT.Mazur.LineSectionBaseChange

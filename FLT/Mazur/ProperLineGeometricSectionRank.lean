/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineGeometricFiberLocus
public import FLT.Mazur.ProperLineRankOneCohomology

/-!
# Intrinsic section rank and cartesian base change

Compute the dimension of actual degree-zero cohomology over the point's
residue field. It is unchanged by cartesian base change, and on affine
acyclic families it equals the rank defining the constructed rank-one open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve

/-- The dimension of actual sections on the geometric residue fiber. -/
def properLineFiberSectionRank {X S : Scheme.{0}} (f : X ⟶ S) (L : X.Modules) (s : S) : ℕ :=
  Module.finrank (S.residueField s)
    (ModuleScalarH (k := S.residueField s) (f.fiberToSpecResidueField s)
      ((pullback (f.fiberι s)).obj L) 0)

/-- The intrinsic section rank is unchanged by every cartesian base change. -/
theorem properLineFiberSectionRank_baseChange {P X T S : Scheme.{0}}
    {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} [IsProper f] {g : T ⟶ S}
    (h : IsPullback p q f g) (L : X.Modules) (hL : LocallyFreeRankOne L) (t : T) :
    properLineFiberSectionRank q ((pullback p).obj L) t =
      properLineFiberSectionRank f L (g t) := by
  let k : q.fiber t ⟶ f.fiber (g t) :=
    Limits.pullback.map _ _ _ _ p (Spec.map (g.residueFieldMap t)) g h.w.symm (by simp)
  have hk : IsPullback k (q.fiberToSpecResidueField t)
      (f.fiberToSpecResidueField (g t)) (Spec.map (g.residueFieldMap t)) :=
    isPullback_fiberToSpecResidueField_of_isPullback h t
  have he : k ≫ f.fiberι (g t) = q.fiberι t ≫ p := by
    simp [k, Scheme.Hom.fiberι]
  let e := (pullbackComp (q.fiberι t) p).app L ≪≫
    (pullbackCongr he.symm).app L ≪≫ ((pullbackComp k (f.fiberι (g t))).app L).symm
  let _ : IsProper (f.fiberToSpecResidueField (g t)) :=
    inferInstanceAs (IsProper (Limits.pullback.snd f _))
  let _ := (hL.pullback (f.fiberι (g t))).isFinitePresentation
  let d := ((moduleScalarHFunctor (q.fiberToSpecResidueField t) 0).mapIso e).toLinearEquiv
  exact d.finrank_eq.trans (proper_field_cohomology_finrank hk _ 0)

end FLT.Mazur.FCurve

namespace FLT.Mazur.LineSectionBaseChange
open FCurve
variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

/-- The affine rank-one open is exactly the intrinsic geometric section-rank-one locus. -/
theorem properLineRankOneOpen_geometric_iff (s : S) :
    s ∈ properLineRankOneOpen f L hL hV ↔ properLineFiberSectionRank f L s = 1 := by
  have hh := properLineRankOneOpen_field_iff (K := S.residueField s) f L hL hV
    (IsPullback.of_hasPullback f (S.fromSpecResidueField s))
    (IsLocalRing.closedPoint (S.residueField s))
  have hs := S.fromSpecResidueField_apply s (IsLocalRing.closedPoint (S.residueField s))
  exact (congrArg (fun x : S ↦ x ∈ properLineRankOneOpen f L hL hV) hs).to_iff.symm.trans hh

end FLT.Mazur.LineSectionBaseChange

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesHZeroFinite

/-!
# Stability of the actual H0 image filtration

Finite generation proved using the proper Rees model gives stability of the
original image filtration. Its eventual powers give the reverse containment
between the image topology and the base-adic topology in degree zero.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening FLT.Mazur.Chow.AffineBase
open FLT.Mazur.FCurve FLT.Mazur.IdealAdicQuotient

namespace FLT.Mazur.BaseAdicCohomology

variable {R : CommRingCat.{0}} [IsNoetherianRing R]
  {X : Scheme.{0}} [X.IsSeparated] (f : X ⟶ Spec R) [IsProper f] (J : Ideal R)
  (M : X.Modules) [M.IsFinitePresentation]

/-- The Rees submodule of the actual degree-zero image filtration is finitely generated. -/
theorem imageFiltration_hZero_fg : (imageFiltration f J M 0).submodule.FG := by
  let _ := Chow.source_isNoetherian f
  exact Module.Finite.iff_fg.mp (BaseAdicRees.imageHZeroRees_finite f J M)

/-- The actual H0 image filtration is stable, as a consequence of geometric finite generation. -/
theorem imageFiltration_hZero_stable : (imageFiltration f J M 0).Stable := by
  apply (Ideal.Filtration.submodule_fg_iff_stable _ (fun n ↦ ?_)).mp
    (imageFiltration_hZero_fg f J M)
  exact Module.Finite.iff_fg.mp (imageFiltration_finite f J M 0 n)

/-- Far enough in the actual H0 filtration, every term is an ordinary ideal power multiple. -/
theorem imageFiltration_hZero_eventual :
    ∃ c, ∀ n ≥ c, (imageFiltration f J M 0).N n =
      J ^ (n - c) • (imageFiltration f J M 0).N c :=
  (imageFiltration_hZero_stable f J M).exists_pow_smul_eq_of_ge

/-- A uniform shift gives the reverse containment into the ordinary H0 adic filtration. -/
theorem imageFiltration_hZero_le_adic :
    ∃ c, ∀ n, (imageFiltration f J M 0).N (n + c) ≤
      J ^ n • (⊤ : Submodule R (ModuleRingH (baseCohomologyScalars f) M 0)) := by
  obtain ⟨c, hc⟩ := imageFiltration_hZero_eventual f J M
  refine ⟨c, fun n ↦ ?_⟩
  rw [hc (n + c) (Nat.le_add_left c n), Nat.add_sub_cancel]
  exact smul_mono_right _ le_top

end FLT.Mazur.BaseAdicCohomology

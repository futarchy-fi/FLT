/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesCohomologyFinite

/-!
# Stability of the actual cohomology image filtration

Finite generation proved using the proper Rees model gives stability of the
original image filtration. Its eventual powers give the reverse containment
between the image topology and the base-adic topology in every degree.
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
  (M : X.Modules) [M.IsFinitePresentation] (q : ℕ)

/-- The Rees submodule of the actual all-degree image filtration is finitely generated. -/
theorem imageFiltration_cohomology_fg : (imageFiltration f J M q).submodule.FG := by
  let _ := Chow.source_isNoetherian f
  exact Module.Finite.iff_fg.mp (BaseAdicRees.imageCohomologyRees_finite f J M q)

/-- Geometric finite generation makes the actual cohomology image filtration stable. -/
theorem imageFiltration_cohomology_stable : (imageFiltration f J M q).Stable := by
  apply (Ideal.Filtration.submodule_fg_iff_stable _ (fun n ↦ ?_)).mp
    (imageFiltration_cohomology_fg f J M q)
  exact Module.Finite.iff_fg.mp (imageFiltration_finite f J M q n)

/-- Every sufficiently late filtration term is an ordinary ideal power multiple. -/
theorem imageFiltration_cohomology_eventual :
    ∃ c, ∀ n ≥ c, (imageFiltration f J M q).N n =
      J ^ (n - c) • (imageFiltration f J M q).N c :=
  (imageFiltration_cohomology_stable f J M q).exists_pow_smul_eq_of_ge

/-- A uniform shift gives the reverse containment into the ordinary cohomology adic filtration. -/
theorem imageFiltration_cohomology_le_adic :
    ∃ c, ∀ n, (imageFiltration f J M q).N (n + c) ≤
      J ^ n • (⊤ : Submodule R (ModuleRingH (baseCohomologyScalars f) M q)) := by
  obtain ⟨c, hc⟩ := imageFiltration_cohomology_eventual f J M q
  refine ⟨c, fun n ↦ ?_⟩
  rw [hc (n + c) (Nat.le_add_left c n), Nat.add_sub_cancel]
  exact smul_mono_right _ le_top

end FLT.Mazur.BaseAdicCohomology

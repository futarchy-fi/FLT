/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterRankOne
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Character bases through a prescribed generic identification

Transfer the given scalar module structure through the actual generic
bijection. This allows the rank-one theorem to apply directly to the
extremal models whose scalar maps were constructed in C5m7.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R K F : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [Field F] [Finite F]
  {X M : FF R K} [Module F X.Points]

/-- Identified integral scalar lifts have derived rank-one character bases. -/
theorem GenericGaloisHom.integralCharacter_basis (f : GenericGaloisHom X M)
    (hf : Function.Bijective f) (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
    (hdim : Module.finrank F X.Points = 1)
    (lift : F → ModelHom M M) (h1 : lift 1 = BialgHom.id R M.CoordinateRing)
    (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
    (hlift : ∀ a x, genericHom (lift a) (f x) = f (a • x)) (χ : Fˣ →* Rˣ) :
    Nonempty (Module.Basis Unit R (M.integralCharacter lift h1 hmul χ)) := by
  let e : M.Points ≃+ X.Points := (AddEquiv.ofBijective f.toAddMonoidHom hf).symm
  let : Module F M.Points := e.module F
  have hdimM : Module.finrank F M.Points = 1 := (e.linearEquiv F).finrank_eq.trans hdim
  have hpoint (a : F) (y : M.Points) : genericHom (lift a) y = a • y := by
    obtain ⟨x, rfl⟩ := hf.2 y
    rw [hlift]
    exact (e.linearEquiv F).symm.map_smul a x
  exact M.exists_integralCharacter_basis p lift h1 hmul hdimM hpoint χ

end ThreeAdicPlan

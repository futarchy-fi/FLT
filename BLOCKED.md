# Serre quotient curve leaf: blocked geometric step

Checked at 2026-09-24 UTC in `/srv/agent-data/home/workspaces/fermat/wt-serre-l6`.

The module `FLT/FreyCurve/Serre/QuotientCurve.lean` now proves the algebraic and descent
consequences of a geometric quotient, including `galois_fixed_sum_of_equiv`, a finite-sum
lemma for the Galois-invariance step in Vélu's formulas.  The module imports alphabetically
from `FLT.lean`, builds successfully, and passes the module linter.  The earlier three
point-level lemmas remain fully proved and use no new axioms.

The requested leaf cannot be completed from the current repository.  No definition or
theorem constructs an isogeny, a quotient Weierstrass curve, or Vélu's point map.  The
available finite-flat quotient infrastructure only constructs a quotient Hopf algebra and
does not provide a Weierstrass curve, an additive point map, its exact kernel, or a proof that
the resulting discriminant is nonzero.  The existing Tate and finite-flat statements do not
fill this gap.

The exact next statement needed before the point-level lemmas can assemble the leaf is:

```lean
theorem exists_geometric_quotient
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) [Fact p.Prime]
    (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
    (hq : Function.Surjective q)
    (hfixed : ∀ g v, q (E.torsionGaloisRepresentation p g v) = q v) :
    ∃ (E' : WeierstrassCurve ℚ), E'.IsElliptic ∧
      ∃ ψ : (E⁄(AlgebraicClosure ℚ)).Point →+ (E'⁄(AlgebraicClosure ℚ)).Point,
        (∀ (g : Field.absoluteGaloisGroup ℚ) v,
          ψ (Affine.Point.map (W' := E) g.toAlgHom v) =
            Affine.Point.map (W' := E') g.toAlgHom (ψ v)) ∧
        (∀ v, ψ v = 0 ↔
          ∃ t : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p,
            q t = 0 ∧ t.val = v)
```

Proving this requires the missing Vélu construction: define and verify the coefficient sums,
show the target discriminant is nonzero, prove the rational map preserves the curve equation
and addition, and establish its exact kernel and Galois equivariance.

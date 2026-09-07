# Mazur D8 page-level audit (hub-lsb1u.2.6)

Audit date: 2026-09-07.  This resolves PQ1 in `mazur-reconciled.md` against
Mazur's primary paper and Snowden's theorem-level exposition.

## Verdict

The reconciled D8 statement is **not faithful to Mazur 1977**.  It conflates
three different arguments:

1. Mazur's torsion proof in Chapter III §5, pp. 156--160;
2. the formal-immersion method used in the later prime-isogeny/winding-quotient
   literature; and
3. P1's valid but non-primary `lambda = 1` specialization of the isogeny
   trace-bound argument.

The primary D8 path must be frozen as Mazur's §5 criterion.  It uses neither a
formal immersion nor Atkin--Lehner cusp-swapping.  Formal immersion remains an
optional alternative path (D7a/D7b), not a predecessor of primary D8.

## 1. What Mazur 1977 actually proves

The theorem is **Chapter III, Theorem 5.1**, printed p. 156, not “Theorem 8”.
It is the complete 15-group torsion classification.  Corollaries 5.2 and 5.3
give the order bound and the cusps-only statement for `X_1(m)`.  The prime-order
reduction in the paper only needs `N >= 23` because contemporary small-level
results had already handled the lower cases; the reusable argument is written
for prime `N > 7`, `N != 13`.

The proof-level chain on printed pp. 157--160 is:

| Page | Step | Exact load-bearing content |
|---|---|---|
| 157--158 | First/second reductions | A rational `N`-torsion point gives `Z/N` in `E[N]`; if the extension by `mu_N` splits, iteration gives an infinite `N`-isogeny chain. Finiteness of `X_0(N)(Q)` (from a nonconstant map to an abelian variety with torsion Mordell--Weil group) forces repetition and an impossible non-scalar endomorphism over `Q`. |
| 158 | Third reduction | It suffices to prove the degree-`N` extension `L/Q(mu_N)` is everywhere unramified. Herbrand's theorem then places it in the `chi^-1` part and would force `N | numerator(B_2)`; since `B_2=1/6`, the extension is trivial. |
| 158--159, Step 1 | Semistability | Additive reduction is excluded using component groups, a bounded ramification extension, Neron models and uniqueness of finite-flat prolongations. |
| 159, Step 2 | The small fibres 2 and 3 | Good reduction would inject the order-`N` point into `E(F_q)`, contradicting `N <= q+1+2 sqrt(q)` for `q=2,3`; multiplicative identity components have too few points as well. Thus reduction is multiplicative and the constant subgroup lies outside the identity component. |
| 159--160, Step 3 | Global use of the Eisenstein quotient | If the constant subgroup lay inside the identity component at another bad prime `q`, the modular point `x` would reduce to one cusp at 3 and the other at `q`. Since the quotient has torsion rational points and torsion specialization is injective away from 2, the two image sections would coincide, contradicting the nonzero image of `[0]-[infinity]`. |
| 160, Step 4 | Local-to-global finish | Good and bad primes now give a split finite-flat `E[N] = Z/N x mu_N` locally, so `L/Q(mu_N)` is unramified. The third reduction and then the infinite-isogeny argument finish. |

The char-2 concern is resolved explicitly: the comparison in Step 3 uses the
prime 3 and primes represented by closed points of
`T = Spec Z[1/(2N)]`; the specialization theorem is invoked only where 2 is
invertible.  The prime 2 is used for the small-fibre exclusion, not for injecting
torsion on the quotient.  No `w_N` occurs in this chain.

The general theorem-level interface isolated by Snowden from this proof is:

```text
N > 7 prime,
A/Q has good reduction away from N,
A(Q) has rank zero (hence is finite by Mordell--Weil),
f : X_0(N) -> A,
f(0) != f(infinity)
-----------------------------------
no E/Q has a rational point of order N.
```

For FLT it is cleaner to require `Finite A(Q)` directly: that is exactly what
D6 supplies and avoids importing finite generation merely to turn rank zero into
finiteness.

## 2. The `lambda = 1` trace splice

P1's alternative is mathematically valid **conditional on its stated isogeny
predecessor**, but it is not Mazur's 1977 derivation.  A rational point of prime
order `ell` makes the isogeny character `lambda` trivial.  Once the isogeny
argument proves potentially good reduction at 3, the characteristic polynomial
of a Frobenius lift has integral trace `a_3`, satisfies `|a_3| <= 2 sqrt(3)`, and
has `1` as a root modulo `ell`.  Hence

```text
ell divides 1 - a_3 + 3 = 4 - a_3.
```

Since `a_3` is an integer and `2 sqrt(3) < 4`, one has
`a_3 in {-3,...,3}` and therefore `1 <= 4-a_3 <= 7`; this is impossible for
`ell >= 11`.  The alleged `a_3 = 4` boundary cannot occur.  Potentially good
additive reduction is legitimate here: the cited trace lemma passes to a totally
ramified extension with the same residue field and then applies Hasse--Weil.

Cost warning: the splice consumes the prime-isogeny theorem's formal-immersion
and potentially-good-reduction stack.  It is shorter only if D7a/D7b and that
isogeny predecessor are already available; it is not a cheap replacement for
Mazur's Chapter III endgame.

## 3. Frozen D8 and dependency repair

Primary D8 is the Mazur/Snowden criterion above, expanded into separately named
obligations for semistability, the 2/3 fibre calculation, the global bad-prime
Step 3, local splitting/unramifiedness, Herbrand, and infinite-isogeny finiteness.
It consumes the fork-independent D6 output recorded in
`mazur-d6-audit.md`: a quotient map with finite rational points and distinct cusp
images.  It does **not** consume cotangent injectivity, formal immersion or
Atkin--Lehner.

The old one-line D8 (“reduces to a cusp; formal immersion forces equality”) is
retired.  It was not merely under-cited: it skipped the unramified/Herbrand and
infinite-isogeny parts of the primary proof.

## Sources

- Mazur, *Modular curves and the Eisenstein ideal*, Publ. Math. IHES 47
  (1977), Chapter III §5, printed pp. 156--160:
  https://www.numdam.org/item/PMIHES_1977__47__33_0.pdf
- Snowden, Math 679, Lecture 18 (explicitly identifies the criterion with Mazur
  III §5):
  https://public.websites.umich.edu/~asnowden/teaching/2013/679/L18.html
- Michaud-Jacobs, *Mazur's isogeny theorem*, Lemma 4.2 (potentially-good trace
  bound):
  https://arxiv.org/abs/2209.03153

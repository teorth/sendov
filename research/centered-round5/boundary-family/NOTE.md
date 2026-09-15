# A feasible nonreal positive-variance boundary family

This note proves a generic family statement, not a numerical optimization result. It also explains the literal C-near gap's supremum, conditional on acceptance of the global C-near paper theorem. It makes no claim about a sharp normalized gap or about a global E_fin<=h/2 bound.

For any real 0<h<=1/10, set a=1-h, m=7, take six copies of q=1 and one copy

    q7=(1-h^4+2i h²)/(1+h^4).

Every pointwise norm equals1, because (1-h^4)²+4h^4=(1+h^4)². The actual mean and variance are

    mu=[7+5h^4+2i h²]/[7(1+h^4)],
    v=24h^4/[49(1+h^4)]>0.

In particular the mean is nonreal for every member of this family; it is not a zero-variance proxy.

## Exact FULLpolar feasibility on the entire interval

Write d=1-a² and A(t)=a+dt. Let

    K0=int_0^1 A(t)^7 dt.

The exact binomial expansion gives K0=1+h²P(h), where

    P(h)=7/2-7h-(7/2)h²+(7/2)h³+(39/4)h^4-3h^5-9h^6
         +(5/2)h^7+(19/4)h^8-2h^9-h^10+(3/4)h^11-(1/8)h^12.

For 0<=h<=1/10, drop the positive nonconstant terms and evaluate each negative term at h=1/10. The resulting exact rational lower bound is greater than27/10. Thus K0>=1+(27/10)h² throughout the interval. `verify.py` reconstructs this polynomial from the original binomial integral and checks that lower bound exactly; it does not infer it from a mesh.

For the actual nonreal family the full complex integral is

    K=int_0^1 A(t)^6 [a+dt q7]dt.

Its real part is

    Re K=K0-d(1-Re q7)int_0^1 t A(t)^6dt.

Here 0<A(t)<=11/10, and (11/10)^6/2<1, so the last integral is less than1. Since d<=2h and 1-Re q7=2h^4/(1+h^4)<=2h^4, the loss is at most4h^5<=h²/250. Therefore

    |K| >= Re K >= 1+(337/125)h² >1.

This is the original FULLpolar integral, not its moment or endpoint-chord relaxation.

## Literal gap and the endpoint optimization issue

Define the precise objective

    g=E_fin+Gamma-(1-a|mu|).

As h tends to zero through this family, mu tends to1 and v tends to0. Every denominator in the finite original C sum stays nonzero. Its finitely many square-root coefficients tend to zero, all H endpoints stay bounded, and |1-a mu|^8 tends to zero. Thus E_fin tends to0, Gamma tends to0, and 1-a|mu| tends to0, giving g->0.

The candidate global paper theorem proves g<=-h/20<0 over the entire original domain. If that theorem passes final review, it follows that

    sup g = 0,

and this supremum is not attained. The same conclusion holds after requiring both positive variance and a nonreal mean, because this family has both properties. This is a conditional mathematical supremum statement, not a claim that a numerical optimizer found a maximum. A normalized objective is needed to measure relative stress near a=1.

For example h=1/(30n), n>=1, is an explicit sequence contained in the already kernel-checked lambda<=1/3 region. The family construction and limit do not depend on the degree-band certificates.

## Replay and scope

Run `python3 -B verify.py`. Exact polynomial identities and the generic feasibility constants pass. Four literal rational members, h=1/10,1/30,1/300,1/1000000, additionally reconstruct FULLpolar, actual statistics, every original C/H term and radical bounds with the existing exact rational verifier. These are implementation diagnostics, not the proof of generic feasibility. No global theorem or kernel verification is claimed by this script.

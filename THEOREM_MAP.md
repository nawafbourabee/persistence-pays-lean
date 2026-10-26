# Faithful theorem scope for main_9.pdf

Source: /Users/nawafbou-rabee/Downloads/main_9.pdf, dated 2026-10-25.
Certification status: **Theorem 1, Theorem 2, Proposition 2.4, and Proposition 3.1 are all kernel-checked.** The final certificates are `A1.theorem_one` in `TheoremOneVerified.lean` and `A1.theorem_two_ennreal` in `TheoremTwoComplete.lean`, together with the two proposition certificates listed in [VERIFICATION_REPORT.md](VERIFICATION_REPORT.md). The full dependency audit passed for 3,541 exported declarations using only the standard three logical axioms.

## Certification criterion

A result counts as verified only when its Lean statement contains the mathematical
assumptions actually made in the paper, the concrete laws/kernels are defined,
and its proof is accepted by the Lean kernel without sorry, sorryAx, new axioms,
or a hypothesis which simply assumes the analytic result being proved.
Conditional algebraic lemmas are useful dependencies but are not verification of
Theorem 1, Theorem 2, Proposition 2.4, or Proposition 3.1. Standard foundational
Lean axioms (propext, Classical.choice, Quot.sound) are not new paper-specific
axioms. All verified declarations need a reproducible build and #print axioms.

## Common definitions

- Integer d >= 1; phase space R^d x R^d with Euclidean norm.
- U is C^2; 0 < m <= L; m I <= Hess U(x) <= L I for every x.
- L_H >= 0 and ||Hess U(x)-Hess U(y)|| <= L_H |x-y| for all x,y.
- x_* is the unique minimizer; H(x,v)=U(x)-U(x_*)+|v|^2/2.
- mu_x is the normalized density proportional to exp(-U); phi is the standard
  Gaussian; mu=mu_x x phi. Normalization and needed integrability must be proved.
- kappa=L/m, hbar=h sqrt(L), ell_H=L_H m^(-3/2), h>0.
- O_t(x,v)=(x,exp(-gamma t)v+sqrt(1-exp(-2 gamma t))xi),
  B_s(x,v)=(x,v-s grad U(x)), A_s(x,v)=(x+s v,v), S(x,v)=(x,-v).
- Phi=B_(h/2) o A_h o B_(h/2). K=O_(h/2) Phi O_(h/2), with independent
  Gaussian noise in every half-step.
- Except Proposition 2.4, gamma=2 sqrt(m).
- P is the actual Definition 2.2 epoch kernel for a positive integer E.
  It draws ell~Exp(1) independently at the epoch start, then E times applies
  O_(h/2), accepts Phi iff ell>Delta H and replaces ell by ell-Delta H,
  otherwise applies S and leaves ell unchanged, then applies O_(h/2).
- KL is extended-valued relative entropy; TV is sup_A |p(A)-q(A)|.
  These must refer to actual measures, not unspecified scalar functionals.
- V(w)=v-(h/2)grad U(x), G(x)=h^2|grad U(x)|^2/8.
  tau(w)=U(x+hV)-U(x)-<grad U(x)+grad U(x+hV),hV>/2.

## Headline statements

### Theorem 1 (pp. 8, 26)

For every admissible d,m,L,L_H,U, probability measure nu absolutely continuous
with respect to mu with M2=||dnu/dmu||_(L2(mu))<infinity, and epsilon in (0,1),
put
D=d+log(M2/epsilon),
Lambda=log(2+kappa+ell_H+D),
N=ceil(log(2/epsilon)/log 4).
There is one absolute constant C0, independent of all inputs, and hbar>0 and
integer E>=1 depending only on kappa,ell_H,d,M2,epsilon, such that
TV(nu P^N,mu)<=epsilon and
N E <= C0 Lambda^(3/2)
       (sqrt(kappa D)+sqrt(ell_H) D^(3/4)) log(2/epsilon).
The actual chain uses at most N E+1 gradient evaluations, rejected steps included.
The proof supplies hbar and E, so computational implementability and a gradient
counter should be formalized, not only a real-valued cost expression.
L_H=0 must be handled explicitly, rather than illegal division by zero.

### Theorem 2 (pp. 9, 18)

For the common assumptions, sqrt(m) h<=3/16, each deterministic initial z,
and every integer n>=1, let r=exp(-sqrt(m)h) and
lambda=r^2 sqrt(m)/(4(16+r)).
Then
KL(delta_z K^(n+1),mu)
 <= (17/15) exp(-lambda n h)
      [E_z H(Z_1)+d log(kappa/(2 e hbar^2 (1-sqrt(m)h)))]
    +(16/15)[hbar^2 E_z(U(X_(n+1))-U_*)/4
      +max_(1<=k<=n) {
         L_H h^2 E_z|V_k|^3/(12 lambda)
         +(221/(16 r))hbar^2 E_z|V_k|^2 }].
Also lambda >= sqrt(m)exp(-2sqrt(m)h)/68.
This is an entropy bound involving actual finite-time chain moments; it is not
a uniform invariant-bias theorem. The first smoothing step and n+1 indexing
must not be dropped.

### Proposition 2.4 (pp. 8-9, 32-33)

For integer d>=2 and 0<m<=L, set
U(x)=m x_1^2/2+L sum_(i=2)^d x_i^2/2.
For any gamma>0, 0<hbar<2, either fresh acceptance uniforms or the exact
Definition 2.2 kernel with arbitrary positive integer epoch length E,
initialize the phase law at mu conditioned on x_1<=0 (density <=2).
For every integer n>=0,
n < sqrt(2 kappa)/(4 hbar) (1+hbar^6/64)^((d-1)/2)
implies TV(Law X_n,mu_x)>1/4.
Consequently the same holds whenever
n < (sqrt(2)/8)sqrt(kappa)d^(1/6).
This is position TV and arbitrary friction, including times inside an epoch.
It requires the extended threshold law for the persistent version.

### Proposition 3.1 (pp. 10-11)

For any joint probability law of (X,V) on R^d x R^d, any nondegenerate
Gaussian density g on R^d, and every t in [0,1], define
E_g(t)=KL(Law(X+tV,V),Law(X+tV) x g).
If E_g(0),E_g(1)<infinity, then E_g(t)<=E_g(0)+E_g(1).
No moment assumptions, finite differential entropy assumption, smoothness of
the joint law, or absolute continuity assumption is imposed initially.
The density conclusion is established in Lemma 3.3 from the two finite KLs.
A proof restricted to Gaussian inputs or finite second moments is insufficient.

## Dependency graph

1. Proposition 3.1, strongest version:
   - Lemma 3.2 Gaussian bridge convolution/square-root density inequality;
   - Lemma 3.3 absolute continuity from two finite conditional KL quantities;
   - joint density under linear shear, Tonelli, conditional Cauchy-Schwarz;
   - finite KL => integrable log likelihood; log r<=2(sqrt r-1);
   - all likelihood ratios and null sets handled almost everywhere.
   The entropy/strong-subadditivity proof is optional and does not by itself
   cover the no-moment case.

2. Lemma 2.1:
   - finite-dimensional inner-product algebra for exact Delta H identity;
   - one-dimensional integration by parts along a segment;
   - Hessian bounds, midpoint cancellation, integral(t-1/2)^2=1/12;
   - descent lemma and existence/minimality of x_*.
   Ring identities alone do not verify the regularity/error bounds.

3. Lemma 2.3:
   - Phi volume-preserving Borel bijection, Phi^-1=S Phi S;
   - accepted-region extended involution (w,ell)->(S Phi w,ell-Delta H(w));
   - measurable piecewise change of variables, extended energy preservation;
   - OU preservation of Gaussian measure; composition and marginalization.
   Proving the involution algebra alone does not establish invariant measures.

4. Theorem 2:
   Lemma 2.1 + Proposition 4.12 + Proposition 4.11 + Lemma 4.14.
   Proposition 4.12 uses KL chain rule, Gaussian OU entropy contraction,
   Talagrand/corrector control, volume-preserving entropy identity, and
   a discrete weighted telescoping recurrence.
   Proposition 4.11 uses Corollary 3.5, Lemmas 4.3,4.8,4.9 and Proposition 4.10.
   Lemma 4.14 uses explicit Gaussian conditional density and entropy plus Gibbs
   normalizing-constant estimates.

5. Integrated corrector estimate (Lemma 4.8):
   - smooth free transport (Lemma 4.5/Appendix A);
   - semicontinuity of KL and entropy under W2 convergence (Lemma 4.6);
   - stability/uniqueness of optimal plans (Lemma 4.7);
   - truncation, Gaussian smoothing, reverse Fatou, uniform integrability.

6. Smooth free transport (Appendix A):
   - Brenier existence/uniqueness for absolutely continuous source measures;
   - convex potential locally Lipschitz on full domain;
   - Alexandrov Hessian and distributional Hessian as positive matrix Radon
     measure with absolutely continuous and singular parts;
   - McCann change-of-variables formula n(y)=Z^-1 exp(-U(Ty))det D_a T(y);
   - Gaussian variational entropy bound and matrix eigenvalue/logdet inequality;
   - integration by parts with nonsmooth convex Hessian and cutoff limits;
   - smooth Gaussian-convolution density and conditional mean/covariance bounds;
   - global nonautonomous ODE flow and continuity-equation transport identity;
   - W2 coupling upper bound, Taylor expansion, Riemann-sum limit.

7. Proposition 5.3:
   Lemma 2.3 + Proposition 5.1 + measurable maximal coupling of whole noise
   blocks (Lemma 5.2), using endpoint/path densities and inverse noise map.
   Requires actual joint-law marginal proofs, not a causal coupling assumption;
   then stationary union bound, Cauchy-Schwarz warmness transfer, coupling TV.

8. Theorem 1:
   Proposition 6.1 plus universal parameter selection and elementary bounds.
   Proposition 6.1 uses:
   - Proposition 5.3;
   - Gibbs energy tail Lemma 5.4;
   - stopped drift/moment/exit Lemmas 5.5,5.6;
   - comparison map Lemma 5.7, conditional entropy Lemma 5.8;
   - comparison corrector Proposition 5.9 and entropy Proposition 5.10;
   - comparison density and moment estimates Lemma 5.11;
   - Pinsker, synchronous comparison until stopping, numerical constants.
   The comparison chain differs from the actual algorithm: a final transfer
   back to the actual P kernel is indispensable.

9. Proposition 2.4:
   - invariant measure domination through each step and threshold refresh;
   - union bound crossing argument;
   - exact weighted Gaussian determinant integral rho(omega)=
     (1+omega^6/64)^(-1/2);
   - covariance of tilted Gaussian and quadrant probability arccos(chi)/(2pi);
   - chi=(1-omega^2/2)/(1+omega^4/8), 1-chi<=omega^2;
   - optimized scalar lower bound and cost interpretation.

## External analytic foundations that must be genuinely proved or imported

Brenier theorem; Talagrand transport-entropy inequality for strongly convex
Gibbs measures; Gaussian OU entropy contraction; entropy chain rule,
variational bounds, Pinsker and lower semicontinuity; conditional distribution
kernels and measurable gluing; Gaussian entropy/integrals and concentration;
McCann change of variables; Alexandrov theorem and matrix-valued Radon
Hessians; continuity-equation flow representation; optimal-plan stability.
Bibliographic citations are not Lean proofs. Any unavailable foundation remains
an explicit unfinished dependency, rather than an assumption added to a headline.


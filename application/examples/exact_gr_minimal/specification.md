# Didactic finite model (not an empirical application)

These fixtures demonstrate contract syntax. All timestamps, evidence records and
empirical-mode flags in fixtures are synthetic; they do not certify real data.

## Typed state, sufficiency and primitives
S={*}, X={0,1}, A={0,1}; all actions feasible. The full state is Markov.
alpha selects a=1-x, P gives x'=a, and U retains *. Components are alpha, P, U
and feasibility. No further hard identity forces a target expansion.

## Regime and relevant observables
B=B0=B1=S x {0,1}; h(*,x)=x; g(*,x)=x. The descriptor space is discrete {0,1}.
nu assigns 1/2 to each point. Convergence mode: almost-sure weak convergence of
empirical occupation measures, for every initial probability on B0.
The baseline descriptor law varies across the basin and remains forward-active.

## Property, intervention and target transport
psi(mu) is c when the occupation mean of x converges to the deterministic
constant c, mu-almost surely; otherwise psi(mu)=0. Thus psi is a property of
path laws, not an unrecorded sample-path statistic.
The metric is absolute difference. J0 replaces alpha by the constant action 0;
P, U and feasibility are held fixed. Target grammar: atomic alpha component;
its hard target closure is itself. No quotient/reparameterization is used;
semantic transport is identity and the schedule is stationary (no clock needed).

## Model set and inference procedure
The formal model set is the singleton model defined here; comparison covers both
B1 states, not a sampled majority. There is no sampling uncertainty in this model.
The effect convention is intervention minus baseline. Bounds are exact rationals.
A ROOT node declares these model primitives; it is not empirical source evidence.

# Read-only federation contracts

`federation/contracts.py` declares an exact source pin, capability, numerical or
evidence-only mode, semantic subject digest and detached artifact digest.

`federation/compatibility.py` compares all of them against an **independent
consumer-owned** expected contract and capability allowlist. It never widens
permitted capabilities, turns a numeric report into Lean-verified evidence, or
authorizes execution of remote code.

`federation/exchange.py` reuses the installed exact-file manifest verifier,
requires an independently supplied manifest SHA-256, and rejects any mismatch
with the source or artifact named in the exchange contract. A matching digest
is integrity only; origin authentication still requires a separately trusted
channel. `local_engine.py` exposes only read-only scoped metadata.

These modules are standalone contracts, **not** a live connection to Allfather,
FFBBP, GSCRD or an external intelligence provider. Provider-specific
integration requires its own security, provenance and privacy approval.

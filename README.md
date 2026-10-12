
# UPT-Lean-Repo

Green base: `UPT/Basic.lean` (from MathlibDemo_UPT_Final10_GREEN)

- wiggle = delta = π/3 -1 = 0.0472
- V = (Φ² - v²)²
- stepS n = n + n%2 (even + idempotent)
- N_H = 47201 - 1e6*wiggle

Build:
```
lake update
lake build
```

Collab: each proof in its own file under UPT/
